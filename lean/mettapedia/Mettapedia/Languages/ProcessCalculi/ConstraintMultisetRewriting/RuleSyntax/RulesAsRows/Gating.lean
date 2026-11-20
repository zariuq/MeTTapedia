import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Queries

/-!
# A fixed program, held in the store as code rows

The form of the statement for a program fixed in advance: the step of a fixed program `P` from a
store `s`, against the step of the interpreter `U` from the store holding `s` together with one code
row per rule of `P`, through the representation "the store of `U` without its code rows".

**The fixed programs** (`FixedProgram`): finite lists of rules of the data fragment whose take, read,
none queries, count and collect patterns are data rows (`DataAddressed`). Such rules never take, read or see
a code row, so the code rows are a gate that stays open. A collect pattern sees the same rows in both
stores, moved along `inl` (`matchesAt_gated`, `liftSeen`).

**The store with codes** (`withCodes P s`): occurrences `O ⊕ Fin n`; the rows of `s` at `inl`, the code
of rule `k` at `inr k`.

**The gating relation** (`Gated P s w`): `w` holds the rows of `s` at `inl` and the codes at `inr`, and
its knowledge is the knowledge of `s` together with closed equations between equal codes.

* `gated_forward`, `gated_backward`: firings of `P` at `s` and of the stored-rule program at `w`
  correspond, firing for firing (same rule, same opening, the selection and the claimed seen sets
  moved along `inl`, plus the read of the rule's code row), and results are gated.
* `fixed_program_bisimulation`: composing with the interpreter's bisimulation, **the step of `U` from
  `withCodes P s` and the step of `P` from `s` are strongly bisimilar**, for every fixed program `P`
  and every store `s` of data rows (`fixed_program_start`); `fixed_program_runs` for runs.
* Existence (`demo_run`, `demo_interpreter_run`): the two-rule program of `Examples`, fixed, runs two
  steps from a store of data rows only, and so does `U` from that store with the two code rows. A rule
  with a collect pattern fires through `U` from the store with its code (`tally_interpreter_run`); with
  a wrong claimed set it is refused (`tally_wrong_refused`).

**Why the patterns must be data rows** (`readAny_reads_code`, `readAny_idle_without_codes`): a rule
reading any row by the pattern `var 0` reads a code row in the store with codes, and has no firing at
the empty store without them. For queries (`noRow_fires`, `noRow_interpreter_idle`): the fixed
program asking that no row match `var 0` fires at the empty store, and the interpreter does nothing from
the empty store with that rule's code, which the none pattern sees.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Gating

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Expr
open Examples (DataFragment dataFragment_closed)
open RunTime (ruleCode_injective)

/-! ## Fixed programs and the store with codes -/

/-- **A rule addressing data rows only**: its takes, reads, none queries and count patterns and collect query
patterns are data rows. -/
structure DataAddressed (r : Rule Tm) : Prop where
  take : ∀ p ∈ r.body.take, ∃ t, p = obj t
  read : ∀ p ∈ r.body.read, ∃ t, p = obj t
  query : ∀ c ∈ r.body.checks, kindOf c ≠ .equal → ∃ t, c.pattern = obj t
  collect : ∀ p ∈ r.collect, ∃ t, p = obj t

/-- **A fixed program**: a list of rules of the data fragment addressing data rows. -/
structure FixedProgram where
  rules : List (Rule Tm)
  data : ∀ r ∈ rules, r ∈ DataFragment
  addressed : ∀ r ∈ rules, DataAddressed r

/-- The program of its rules. -/
def FixedProgram.program (P : FixedProgram) : Program Tm := {r | r ∈ P.rules}

variable {O : Type*} [DecidableEq O]

/-- **The store holding `s` and the codes of `P`'s rules.** -/
def withCodes (P : FixedProgram) (s : State Tm O) : State Tm (O ⊕ Fin P.rules.length) :=
  ⟨s.frame, s.knowledge, s.present.map Function.Embedding.inl ∪ Finset.univ.map Function.Embedding.inr,
    Sum.elim s.label fun k => ruleCode (P.rules.get k)⟩

/-- A closed equation between equal terms. -/
def Trivial (e : Equation Expr) : Prop := e.1.closed ∧ e.2.closed ∧ nf e.1 = nf e.2

/-- **The gating relation.** -/
structure Gated (P : FixedProgram) (s : State Tm O) (w : State Tm (O ⊕ Fin P.rules.length)) : Prop where
  present : w.present = s.present.map Function.Embedding.inl ∪ Finset.univ.map Function.Embedding.inr
  data : ∀ o, w.label (.inl o) = s.label o
  codes : ∀ k, w.label (.inr k) = ruleCode (P.rules.get k)
  dataRows : ∀ o ∈ s.present, ∃ t, s.label o = obj t
  knowledge : ∃ C : EquationStore Expr, (∀ e ∈ C, Trivial e) ∧
    ∀ e, e ∈ w.knowledge ↔ e ∈ s.knowledge ∨ e ∈ C

omit [DecidableEq O] in
theorem mem_map_inl {A : Finset O} {K : Type*} (a : O) :
    (Sum.inl a : O ⊕ K) ∈ A.map Function.Embedding.inl ↔ a ∈ A :=
  Finset.mem_map' Function.Embedding.inl

omit [DecidableEq O] in
theorem inl_not_mem_map_inr {K : Type*} [Fintype K] (a : O) :
    (Sum.inl a : O ⊕ K) ∉ (Finset.univ : Finset K).map Function.Embedding.inr := by
  simp

theorem mem_present_inl {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) (o : O) : Sum.inl o ∈ w.present ↔ o ∈ s.present := by
  rw [gated.present, Finset.mem_union, mem_map_inl]
  simp

theorem mem_present_inr {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) (k : Fin P.rules.length) : Sum.inr k ∈ w.present := by
  rw [gated.present]
  simp

/-- **A store of data rows is gated by its store with codes.** -/
theorem withCodes_gated (P : FixedProgram) {s : State Tm O}
    (dataRows : ∀ o ∈ s.present, ∃ t, s.label o = obj t) : Gated P s (withCodes P s) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, dataRows, ⟨[], fun _ inside => by simp at inside,
    fun _ => by simp [withCodes]⟩⟩

/-- **A gated store is a tagged store of the stored-rule program.** -/
theorem gated_tagged {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) : Tagged DataFragment w := by
  intro o present
  cases o with
  | inl o =>
      obtain ⟨t, same⟩ := gated.dataRows o ((mem_present_inl gated o).mp present)
      exact Or.inl ⟨t, (gated.data o).trans same⟩
  | inr k => exact Or.inr ⟨_, P.data _ (List.get_mem _ _), gated.codes k⟩

/-- **Gated stores have the same solutions.** -/
theorem gated_models {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) (σ : ℕ → Expr) : action.Models σ w.knowledge ↔ action.Models σ s.knowledge := by
  obtain ⟨C, trivial, members⟩ := gated.knowledge
  constructor
  · intro solved e inside
    exact solved e ((members e).mpr (Or.inl inside))
  · intro solved e inside
    rcases (members e).mp inside with old | closedE
    · exact solved e old
    · obtain ⟨left, right, same⟩ := trivial e closedE
      show nf (subst σ e.1) = nf (subst σ e.2)
      rw [subst_of_closed _ left, subst_of_closed _ right]
      exact same

/-- **A gated store mentions what the store mentions, and closed codes.** -/
theorem gated_mentions {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) (t : Expr) : w.Mentions t → s.Mentions t ∨ t.closed := by
  obtain ⟨C, trivial, members⟩ := gated.knowledge
  rintro (inside | inside | ⟨o, present, rfl⟩)
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    rcases (members e).mp member with old | closedE
    · exact Or.inl (Or.inl (List.mem_map.mpr ⟨e, old, rfl⟩))
    · exact Or.inr (trivial e closedE).1
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    rcases (members e).mp member with old | closedE
    · exact Or.inl (Or.inr (Or.inl (List.mem_map.mpr ⟨e, old, rfl⟩)))
    · exact Or.inr (trivial e closedE).2.1
  · cases o with
    | inl o =>
        refine Or.inl (Or.inr (Or.inr ⟨o, (mem_present_inl gated o).mp present, ?_⟩))
        exact (gated.data o).symm
    | inr k =>
        rw [gated.codes]
        exact Or.inr (ruleCode_closed (P.data _ (List.get_mem _ _)).1)

/-- **The store mentions only what the gated store mentions.** -/
theorem mentions_gated {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}
    (gated : Gated P s w) (t : Expr) : s.Mentions t → w.Mentions t := by
  obtain ⟨C, -, members⟩ := gated.knowledge
  rintro (inside | inside | ⟨o, present, rfl⟩)
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact Or.inl (List.mem_map.mpr ⟨e, (members e).mpr (Or.inl member), rfl⟩)
  · obtain ⟨e, member, rfl⟩ := List.mem_map.mp inside
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨e, (members e).mpr (Or.inl member), rfl⟩))
  · exact Or.inr (Or.inr ⟨.inl o, (mem_present_inl gated o).mpr present, gated.data o⟩)

/-! ## Corresponding firings -/

section Firings

variable {P : FixedProgram} {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)}

/-- The selection moved along `inl`, with the read of the code row of rule `k` first. -/
def lift (k : Fin P.rules.length) (sel : Selection O) : Selection (O ⊕ Fin P.rules.length) :=
  ⟨sel.taken.map Sum.inl, Sum.inr k :: sel.read.map Sum.inl, sel.made.map Sum.inl⟩

/-- The claimed seen sets moved along `inl`. -/
def liftSeen {K : Type*} (seen : List (Finset O)) : List (Finset (O ⊕ K)) :=
  seen.map fun A => A.map Function.Embedding.inl

/-- The firing of a rule of the fixed program. -/
def objFiring {r : Rule Tm} (member : r ∈ P.program) (a : PUnit.{1}) (ι : ℕ → Expr) (sel : Selection O)
    (seen : List (Finset O)) : Firing O Ext P.program a :=
  ⟨r, member, PUnit.unit, ι, sel, seen⟩

/-- **Freshness moves to the store with codes.** -/
theorem fresh_to_codes (gated : Gated P s w) {r : Rule Tm} (frag : Fragment r) (member : r ∈ P.program)
    {ι : ℕ → Expr} {sel₀ : Selection O} {seen₀ : List (Finset O)}
    (fresh : (objFiring member s.frame ι sel₀ seen₀).Fresh X s) {F : Set (Rule Tm)} (hr : r ∈ F)
    (sel : Selection (O ⊕ Fin P.rules.length)) (seen : List (Finset (O ⊕ Fin P.rules.length))) :
    (storedFiring hr w.frame ι sel seen).Fresh X w := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  refine ⟨u, fun t mentions => ?_, fun t member' => ?_⟩
  · rcases gated_mentions gated t mentions with old | closedT
    · exact onState t old
    · show nf (subst u (subst var t)) = nf (subst g t)
      rw [subst_var, subst_of_closed _ closedT, subst_of_closed _ closedT]
  · have member'' : t = ruleCode r ∨ t ∈ r.terms := by
      unfold Rule.terms at member' ⊢
      simp only [storedFiring, stored, List.mem_append, List.mem_cons] at member' ⊢
      tauto
    rcases member'' with rfl | old
    · show nf (subst u (subst ι (ruleCode r))) = nf (subst h (ruleCode r))
      rw [subst_ruleCode frag, subst_ruleCode frag, subst_ruleCode frag]
    · exact onRule t old

/-- **Freshness moves back to the store without codes.** -/
theorem fresh_from_codes (gated : Gated P s w) {r : Rule Tm} {F : Set (Rule Tm)} (hr : r ∈ F)
    {ι : ℕ → Expr} {sel : Selection (O ⊕ Fin P.rules.length)} {seen : List (Finset (O ⊕ Fin P.rules.length))}
    (fresh : (storedFiring hr w.frame ι sel seen).Fresh X w) (member : r ∈ P.program)
    (sel₀ : Selection O) (seen₀ : List (Finset O)) :
    (objFiring member s.frame ι sel₀ seen₀).Fresh X s := by
  intro b g h
  obtain ⟨u, onState, onRule⟩ := fresh b g h
  refine ⟨u, fun t mentions => onState t (mentions_gated gated t mentions), fun t member' => onRule t ?_⟩
  have member'' : t ∈ r.terms := member'
  unfold Rule.terms at member'' ⊢
  simp only [storedFiring, stored, List.mem_append, List.mem_cons] at member'' ⊢
  tauto

/-- **The informations differ only by the closed code read.** -/
theorem information_gated (gated : Gated P s w) {r : Rule Tm} {k : Fin P.rules.length}
    (member : r ∈ P.program) (hr : r ∈ DataFragment) {ι : ℕ → Expr} (sel : Selection O)
    (seen : List (Finset (O ⊕ Fin P.rules.length))) (seen₀ : List (Finset O)) :
    (storedFiring hr w.frame ι (lift k sel) seen).information X w =
      w.knowledge ++ (objFiring member s.frame ι sel seen₀).matching X s (r.body.take.map (subst ι)) sel.taken ++
        ((subst ι (ruleCode r), subst var (w.label (.inr k))) ::
          (objFiring member s.frame ι sel seen₀).matching X s (r.body.read.map (subst ι)) sel.read) ++
        r.body.tell.map (fun pair => (subst ι pair.1, subst ι pair.2)) := by
  have rows : ∀ o, Firing.row X w (storedFiring hr w.frame ι (lift k sel) seen) (.inl o) =
      Firing.row X s (objFiring member s.frame ι sel seen₀) o := by
    intro o
    show subst var (w.label (.inl o)) = subst var (s.label o)
    rw [gated.data]
  have knowledgeEq : X.applyStore (Ext.weaken (storedFiring hr w.frame ι (lift k sel) seen).ext)
      w.knowledge = w.knowledge := Frames.applyStore_id (X := X) w.knowledge
  have takes : Firing.matching X w (storedFiring hr w.frame ι (lift k sel) seen)
      (Firing.opened X (storedFiring hr w.frame ι (lift k sel) seen)).take
        (storedFiring hr w.frame ι (lift k sel) seen).selection.taken =
        (objFiring member s.frame ι sel seen₀).matching X s (r.body.take.map (subst ι)) sel.taken := by
    show List.zipWith (fun p o => (p, Firing.row X w (storedFiring hr w.frame ι (lift k sel) seen) o))
        (r.body.take.map (subst ι)) (sel.taken.map Sum.inl) =
      List.zipWith (fun p o => (p, Firing.row X s (objFiring member s.frame ι sel seen₀) o))
        (r.body.take.map (subst ι)) sel.taken
    rw [List.zipWith_map_right]
    congr 1
    funext p o
    rw [rows]
  have reads : Firing.matching X w (storedFiring hr w.frame ι (lift k sel) seen)
      (Firing.opened X (storedFiring hr w.frame ι (lift k sel) seen)).read
        (storedFiring hr w.frame ι (lift k sel) seen).selection.read =
        (subst ι (ruleCode r), subst var (w.label (.inr k))) ::
          (objFiring member s.frame ι sel seen₀).matching X s (r.body.read.map (subst ι)) sel.read := by
    show List.zipWith (fun p o => (p, Firing.row X w (storedFiring hr w.frame ι (lift k sel) seen) o))
        (subst ι (ruleCode r) :: r.body.read.map (subst ι)) (Sum.inr k :: sel.read.map Sum.inl) =
      (subst ι (ruleCode r), subst var (w.label (.inr k))) ::
        List.zipWith (fun p o => (p, Firing.row X s (objFiring member s.frame ι sel seen₀) o))
          (r.body.read.map (subst ι)) sel.read
    rw [List.zipWith_cons_cons, List.zipWith_map_right]
    congr 1
    congr 1
    funext p o
    rw [rows]
  unfold Firing.information
  rw [knowledgeEq, takes, reads]
  rfl

omit [DecidableEq O] in
/-- The information of a firing of the fixed program. -/
theorem information_obj {r : Rule Tm} (member : r ∈ P.program) {ι : ℕ → Expr} (sel : Selection O)
    (seen₀ : List (Finset O)) :
    (objFiring member s.frame ι sel seen₀).information X s =
      s.knowledge ++ (objFiring member s.frame ι sel seen₀).matching X s (r.body.take.map (subst ι)) sel.taken ++
        (objFiring member s.frame ι sel seen₀).matching X s (r.body.read.map (subst ι)) sel.read ++
        r.body.tell.map (fun pair => (subst ι pair.1, subst ι pair.2)) := by
  have knowledgeEq : X.applyStore (Ext.weaken (objFiring member s.frame ι sel seen₀).ext)
      s.knowledge = s.knowledge := Frames.applyStore_id (X := X) s.knowledge
  unfold Firing.information
  rw [knowledgeEq]
  rfl

/-- **The code read is a closed equation between equal codes.** -/
theorem code_read_trivial (gated : Gated P s w) {r : Rule Tm} (frag : Fragment r) {k : Fin P.rules.length}
    (coded : P.rules.get k = r) (ι : ℕ → Expr) :
    Trivial (subst ι (ruleCode r), subst var (w.label (.inr k))) := by
  rw [gated.codes, coded, subst_ruleCode frag, subst_ruleCode frag]
  exact ⟨ruleCode_closed frag, ruleCode_closed frag, rfl⟩

/-- **The knowledge after corresponding firings is gated.** -/
theorem knowledge_gated (gated : Gated P s w) {r : Rule Tm} (frag : Fragment r) {k : Fin P.rules.length}
    (coded : P.rules.get k = r) (member : r ∈ P.program) (hr : r ∈ DataFragment) {ι : ℕ → Expr}
    (sel : Selection O) (seen : List (Finset (O ⊕ Fin P.rules.length))) (seen₀ : List (Finset O)) :
    ∃ C : EquationStore Expr, (∀ e ∈ C, Trivial e) ∧
      ∀ e, e ∈ (storedFiring hr w.frame ι (lift k sel) seen).information X w ↔
        e ∈ (objFiring member s.frame ι sel seen₀).information X s ∨ e ∈ C := by
  obtain ⟨C, trivial, members⟩ := gated.knowledge
  refine ⟨(subst ι (ruleCode r), subst var (w.label (.inr k))) :: C, ?_, fun e => ?_⟩
  · intro e inside
    rcases List.mem_cons.mp inside with rfl | old
    · exact code_read_trivial gated frag coded ι
    · exact trivial e old
  · rw [information_gated gated member hr sel seen seen₀, information_obj member sel seen₀]
    simp only [List.mem_append, List.mem_cons, members]
    tauto

/-- **A data pattern never matches a code row.** -/
theorem data_ne_code {t : Expr} (σ ι : ℕ → Expr) {r : Rule Tm} (frag : Fragment r) :
    nf (subst σ (subst ι (obj t))) ≠ nf (subst σ (ruleCode r)) := by
  rw [subst_ruleCode frag, nf_ruleCode frag, subst_obj, subst_obj, nf_obj]
  exact obj_ne_code _ _

/-- **A data pattern matches the same rows in the store with codes**, moved along `inl`. -/
theorem matchesAt_gated (gated : Gated P s w) {p t : Expr} (isData : p = obj t) (ι σ : ℕ → Expr) :
    matchesAt X (b := PUnit.unit) σ w.label w.present (subst ι p) =
      (matchesAt X (b := PUnit.unit) σ s.label s.present (subst ι p)).map Function.Embedding.inl := by
  ext o'
  rw [mem_matchesAt, gated.present]
  cases o' with
  | inl o =>
      rw [Finset.mem_union, mem_map_inl, mem_map_inl, mem_matchesAt, gated.data]
      have notCode := inl_not_mem_map_inr (K := Fin P.rules.length) o
      simp only [notCode, or_false]
  | inr j =>
      refine iff_of_false ?_ (by simp)
      rintro ⟨-, equated⟩
      have equated' : nf (subst σ (subst ι p)) = nf (subst σ (w.label (.inr j))) := equated
      rw [isData, gated.codes] at equated'
      exact data_ne_code σ ι (P.data _ (List.get_mem _ _)).1 equated'

/-- **Collect patterns that are data rows see the claimed sets exactly when they see them moved along
`inl`.** -/
theorem collect_gated (gated : Gated P s w) (ι σ : ℕ → Expr) :
    ∀ (ps : List Expr) (seen₀ : List (Finset O)), (∀ p ∈ ps, ∃ t, p = obj t) →
      ((∀ q ∈ (ps.map (subst ι)).zip (liftSeen seen₀),
          matchesAt X (b := PUnit.unit) σ w.label w.present q.1 = q.2) ↔
        ∀ q ∈ (ps.map (subst ι)).zip seen₀, matchesAt X (b := PUnit.unit) σ s.label s.present q.1 = q.2)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp [liftSeen]
  | p :: ps, A :: seen₀, data => by
      simp only [List.map_cons, liftSeen, List.zip_cons_cons, List.mem_cons, forall_eq_or_imp]
      obtain ⟨t, isData⟩ := data p List.mem_cons_self
      rw [matchesAt_gated gated isData ι σ, Finset.map_inj]
      exact and_congr Iff.rfl
        (collect_gated gated ι σ ps seen₀ fun p' inside => data p' (List.mem_cons_of_mem _ inside))

/-- **The checks and the collect pass at the same solutions.** -/
theorem holds_gated (gated : Gated P s w) {r : Rule Tm} (addressed : DataAddressed r)
    (member : r ∈ P.program) (hr : r ∈ DataFragment) {k : Fin P.rules.length} {ι : ℕ → Expr}
    (sel : Selection O) (seen₀ : List (Finset O)) (σ : ℕ → Expr) :
    (storedFiring hr w.frame ι (lift k sel) (liftSeen seen₀)).Holds X w (b := PUnit.unit) σ ↔
      (objFiring member s.frame ι sel seen₀).Holds X s (b := PUnit.unit) σ := by
  rw [holds_iff_full, holds_iff_full]
  refine and_congr ?_ ?_
  · show (∀ c ∈ r.body.checks, checkHolds X (b := PUnit.unit) σ
        (Firing.row X w (storedFiring hr w.frame ι (lift k sel) (liftSeen seen₀))) w.present (c.map (subst ι))) ↔
      ∀ c ∈ r.body.checks, checkHolds X (b := PUnit.unit) σ
        (Firing.row X s (objFiring member s.frame ι sel seen₀)) s.present (c.map (subst ι))
    rw [row_eq, row_eq]
    refine forall₂_congr fun c inside => ?_
    cases c with
    | equal left right => exact Iff.rfl
    | predicate quantifier pattern =>
        obtain ⟨t, isData⟩ := addressed.query _ inside (by simp [kindOf])
        have isData' : pattern = obj t := isData
        cases quantifier with
        | any =>
            show (∃ o' ∈ w.present, nf (subst σ (subst ι pattern)) = nf (subst σ (w.label o'))) ↔
              ∃ o ∈ s.present, nf (subst σ (subst ι pattern)) = nf (subst σ (s.label o))
            constructor
            · rintro ⟨o', present', same⟩
              cases o' with
              | inl o =>
                  rw [gated.data] at same
                  exact ⟨o, (mem_present_inl gated o).mp present', same⟩
              | inr j =>
                  rw [gated.codes, isData'] at same
                  exact absurd same (data_ne_code σ ι (P.data _ (List.get_mem _ _)).1)
            · rintro ⟨o, present, same⟩
              refine ⟨.inl o, (mem_present_inl gated o).mpr present, ?_⟩
              rw [gated.data]
              exact same
        | none =>
            show (∀ o' ∈ w.present, ¬ nf (subst σ (subst ι pattern)) = nf (subst σ (w.label o'))) ↔
              ∀ o ∈ s.present, ¬ nf (subst σ (subst ι pattern)) = nf (subst σ (s.label o))
            constructor
            · intro all o present
              have := all (.inl o) ((mem_present_inl gated o).mpr present)
              rwa [gated.data] at this
            · intro all o' present'
              cases o' with
              | inl o =>
                  rw [gated.data]
                  exact all o ((mem_present_inl gated o).mp present')
              | inr j =>
                  rw [gated.codes, isData']
                  exact data_ne_code σ ι (P.data _ (List.get_mem _ _)).1
    | count pattern number =>
        obtain ⟨t, isData⟩ := addressed.query _ inside (by simp [kindOf])
        have isData' : pattern = obj t := isData
        show (matchesAt X (b := PUnit.unit) σ w.label w.present (subst ι pattern)).card = number ↔
          (matchesAt X (b := PUnit.unit) σ s.label s.present (subst ι pattern)).card = number
        rw [matchesAt_gated gated isData' ι σ, Finset.card_map]
  · rw [row_eq, row_eq]
    exact collect_gated gated ι σ r.collect seen₀ addressed.collect

end Firings

/-! ## Gated steps -/

section Steps

variable {P : FixedProgram}

omit [DecidableEq O] in
theorem models_of_members {A B C : EquationStore Expr} (trivial : ∀ e ∈ C, Trivial e)
    (members : ∀ e, e ∈ A ↔ e ∈ B ∨ e ∈ C) (σ : ℕ → Expr) :
    action.Models σ A ↔ action.Models σ B := by
  constructor
  · intro solved e inside
    exact solved e ((members e).mpr (Or.inl inside))
  · intro solved e inside
    rcases (members e).mp inside with old | closedE
    · exact solved e old
    · obtain ⟨left, right, same⟩ := trivial e closedE
      show nf (subst σ e.1) = nf (subst σ e.2)
      rw [subst_of_closed _ left, subst_of_closed _ right]
      exact same

theorem relabel_inl {K : Type*} [DecidableEq K] {rowW : O ⊕ K → Tm PUnit.unit} {rowS : O → Tm PUnit.unit}
    (rows : ∀ o, rowW (.inl o) = rowS o) :
    ∀ (made : List O) (terms : List (Tm PUnit.unit)) (o : O),
      relabel rowW (made.map Sum.inl) terms (.inl o) = relabel rowS made terms o
  | [], _, o => rows o
  | _ :: _, [], o => rows o
  | m :: rest, t :: ts, o => by
      simp only [List.map_cons, relabel, Sum.inl.injEq]
      split_ifs
      · rfl
      · exact relabel_inl rows rest ts o

omit [DecidableEq O] in
theorem exists_map_inl {K : Type*} : ∀ {l : List (O ⊕ K)}, (∀ x ∈ l, ∃ o, x = .inl o) →
    ∃ l₀ : List O, l = l₀.map Sum.inl
  | [], _ => ⟨[], rfl⟩
  | x :: rest, all => by
      obtain ⟨o, rfl⟩ := all x List.mem_cons_self
      obtain ⟨l₀, rfl⟩ := exists_map_inl fun y inside => all y (List.mem_cons_of_mem _ inside)
      exact ⟨o :: l₀, rfl⟩

/-- **The selection moved along `inl` is enabled exactly when the selection is.** -/
theorem enabled_lift {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)} (gated : Gated P s w)
    (k : Fin P.rules.length) (sel : Selection O) :
    Enabled (fun _ : O ⊕ Fin P.rules.length => ()) w.present ((lift k sel).commit (T := Unit)) ↔
      Enabled (fun _ : O => ()) s.present (sel.commit (T := Unit)) := by
  constructor
  · intro enabled
    refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, ?_, fun query inside => by
      simp [Selection.commit] at inside⟩
    · have taken : Sum.inl o ∈ ((lift k sel).commit (T := Unit)).taken := by
        simpa [Selection.commit, lift] using inside
      exact (mem_present_inl gated o).mp (enabled.taken_subset taken)
    · have read : Sum.inl o ∈ ((lift k sel).commit (T := Unit)).kept := by
        simpa [Selection.commit, lift] using inside
      exact (mem_present_inl gated o).mp (enabled.kept_subset read)
    · rw [Finset.disjoint_left]
      intro o taken read
      have taken' : Sum.inl o ∈ ((lift k sel).commit (T := Unit)).taken := by
        simpa [Selection.commit, lift] using taken
      have read' : Sum.inl o ∈ ((lift k sel).commit (T := Unit)).kept := by
        simpa [Selection.commit, lift] using read
      exact Finset.disjoint_left.mp enabled.apart taken' read'
    · rw [Finset.disjoint_left]
      intro o made present
      have made' : Sum.inl o ∈ ((lift k sel).commit (T := Unit)).made := by
        simpa [Selection.commit, lift] using made
      exact Finset.disjoint_left.mp enabled.fresh made' ((mem_present_inl gated o).mpr present)
  · intro enabled
    refine ⟨fun x inside => ?_, fun x inside => ?_, ?_, ?_, fun query inside => by
      simp [Selection.commit] at inside⟩
    · simp only [Selection.commit, lift, List.mem_toFinset, List.mem_map] at inside
      obtain ⟨o, taken, rfl⟩ := inside
      exact (mem_present_inl gated o).mpr (enabled.taken_subset (by simpa [Selection.commit] using taken))
    · simp only [Selection.commit, lift, List.mem_toFinset, List.mem_cons, List.mem_map] at inside
      rcases inside with rfl | ⟨o, read, rfl⟩
      · exact mem_present_inr gated k
      · exact (mem_present_inl gated o).mpr (enabled.kept_subset (by simpa [Selection.commit] using read))
    · rw [Finset.disjoint_left]
      intro x taken read
      simp only [Selection.commit, lift, List.mem_toFinset, List.mem_map] at taken
      obtain ⟨o, takenO, rfl⟩ := taken
      have read' : o ∈ sel.read := by simpa [Selection.commit, lift] using read
      exact Finset.disjoint_left.mp enabled.apart (by simpa [Selection.commit] using takenO)
        (by simpa [Selection.commit] using read')
    · rw [Finset.disjoint_left]
      intro x made present
      simp only [Selection.commit, lift, List.mem_toFinset, List.mem_map] at made
      obtain ⟨o, madeO, rfl⟩ := made
      exact Finset.disjoint_left.mp enabled.fresh (by simpa [Selection.commit] using madeO)
        ((mem_present_inl gated o).mp present)

/-- **Corresponding firings: admission agrees and results are gated.** -/
theorem gated_pair {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)} (gated : Gated P s w)
    {r : Rule Tm} (member : r ∈ P.program) {k : Fin P.rules.length} (coded : P.rules.get k = r)
    {ι : ℕ → Expr} (sel : Selection O) (seen₀ : List (Finset O))
    (freshS : (objFiring member s.frame ι sel seen₀).Fresh X s) :
    ((storedFiring (P.data r member) w.frame ι (lift k sel) (liftSeen seen₀)).Admits X w ↔
      (objFiring member s.frame ι sel seen₀).Admits X s) ∧
      ((objFiring member s.frame ι sel seen₀).Admits X s →
        Gated P ((objFiring member s.frame ι sel seen₀).result X s)
          ((storedFiring (P.data r member) w.frame ι (lift k sel) (liftSeen seen₀)).result X w)) := by
  have hr := P.data r member
  have frag := hr.1
  have addressed := P.addressed r member
  have freshW := fresh_to_codes gated frag member freshS hr (lift k sel) (liftSeen seen₀)
  obtain ⟨C, trivial, members⟩ := knowledge_gated gated frag coded member hr sel (liftSeen seen₀) seen₀
  have modelsIff := models_of_members trivial members
  have holdsIff := holds_gated gated addressed member hr (k := k) (ι := ι) sel seen₀
  have liftedLength : (liftSeen seen₀ : List (Finset (O ⊕ Fin P.rules.length))).length = seen₀.length :=
    List.length_map _
  refine ⟨⟨fun admitted => ?_, fun admitted => ?_⟩, fun admitted => ?_⟩
  · obtain ⟨⟨-, takenNodup, madeNodup, takeLength, readLength, produceLength, collectLength⟩, enabled,
      ⟨_, τ, solved⟩, asks⟩ := admitted
    have takeLength' : r.body.take.length = (sel.taken.map Sum.inl).length := takeLength
    have readLength' : (ruleCode r :: r.body.read).length = (Sum.inr k :: sel.read.map Sum.inl).length :=
      readLength
    have produceLength' : r.body.produce.length = (sel.made.map Sum.inl).length := produceLength
    have collectLength' : r.collect.length = (liftSeen seen₀ : List (Finset (O ⊕ Fin P.rules.length))).length :=
      collectLength
    refine ⟨⟨freshS, ?_, ?_, ?_, ?_, ?_, collectLength'.trans liftedLength⟩, (enabled_lift gated k sel).mp enabled,
      ⟨PUnit.unit, τ, (modelsIff τ).mp solved⟩, fun b σ solvedS => (holdsIff σ).mp
        (asks PUnit.unit σ ((modelsIff σ).mpr solvedS))⟩
    · exact (List.nodup_map_iff Sum.inl_injective).mp takenNodup
    · exact (List.nodup_map_iff Sum.inl_injective).mp madeNodup
    · show r.body.take.length = sel.taken.length
      simpa using takeLength'
    · show r.body.read.length = sel.read.length
      simpa using readLength'
    · show r.body.produce.length = sel.made.length
      simpa using produceLength'
  · obtain ⟨⟨-, takenNodup, madeNodup, takeLength, readLength, produceLength, collectLength⟩, enabled,
      ⟨_, τ, solved⟩, asks⟩ := admitted
    have takeLength' : r.body.take.length = sel.taken.length := takeLength
    have readLength' : r.body.read.length = sel.read.length := readLength
    have produceLength' : r.body.produce.length = sel.made.length := produceLength
    have collectLength' : r.collect.length = seen₀.length := collectLength
    have takenNodup' : sel.taken.Nodup := takenNodup
    have madeNodup' : sel.made.Nodup := madeNodup
    refine ⟨⟨freshW, ?_, ?_, ?_, ?_, ?_, collectLength'.trans liftedLength.symm⟩,
      (enabled_lift gated k sel).mpr enabled,
      ⟨PUnit.unit, τ, (modelsIff τ).mpr solved⟩, fun b σ solvedW => (holdsIff σ).mpr
        (asks PUnit.unit σ ((modelsIff σ).mp solvedW))⟩
    · exact (List.nodup_map_iff Sum.inl_injective).mpr takenNodup'
    · exact (List.nodup_map_iff Sum.inl_injective).mpr madeNodup'
    · show r.body.take.length = (sel.taken.map Sum.inl).length
      simpa using takeLength'
    · show (ruleCode r :: r.body.read).length = (Sum.inr k :: sel.read.map Sum.inl).length
      simpa using readLength'
    · show r.body.produce.length = (sel.made.map Sum.inl).length
      simpa using produceLength'
  · obtain ⟨⟨-, -, madeNodup, -, -, produceLength, -⟩, -, -, -⟩ := admitted
    have madeNodup' : sel.made.Nodup := madeNodup
    have produceLength' : r.body.produce.length = sel.made.length := produceLength
    have rows : ∀ o, Firing.row X w (storedFiring hr w.frame ι (lift k sel) (liftSeen seen₀)) (.inl o) =
        Firing.row X s (objFiring member s.frame ι sel seen₀) o := by
      intro o
      show subst var (w.label (.inl o)) = subst var (s.label o)
      rw [gated.data]
    refine ⟨?_, fun o => relabel_inl rows sel.made _ o, fun j => ?_, ?_, ⟨C, trivial, members⟩⟩
    · ext x
      show x ∈ fire w.present _ ↔ x ∈ (fire s.present _).map Function.Embedding.inl ∪
        Finset.univ.map Function.Embedding.inr
      rw [gated.present]
      cases x with
      | inl o => simp [mem_fire, Selection.commit, lift, storedFiring, objFiring]
      | inr j => simp [mem_fire, Selection.commit, lift, storedFiring, objFiring]
    · show relabel _ (sel.made.map Sum.inl) _ (.inr j) = _
      rw [Firing.relabel_of_not_mem _ _ _ (by simp)]
      show subst var (w.label (.inr j)) = _
      rw [gated.codes, subst_ruleCode (P.data _ (List.get_mem _ _)).1]
    · intro o present
      by_cases made : o ∈ sel.made
      · obtain ⟨j, inside, rfl⟩ := List.mem_iff_getElem.mp made
        have insideP : j < r.body.produce.length := produceLength' ▸ inside
        have zipped := Firing.relabel_zip (Firing.row X s (objFiring member s.frame ι sel seen₀))
          sel.made (r.body.produce.map (subst ι)) madeNodup' (by simpa using produceLength'.symm)
          (sel.made[j], subst ι (r.body.produce[j]'insideP)) (by
            have below : j < (sel.made.zip (r.body.produce.map (subst ι))).length := by
              rw [List.length_zip, List.length_map, produceLength', min_self]
              exact inside
            have entry := List.getElem_mem below
            rw [List.getElem_zip, List.getElem_map] at entry
            exact entry)
        obtain ⟨t, same⟩ := hr.2 _ (List.getElem_mem insideP)
        refine ⟨subst ι t, zipped.trans ?_⟩
        show subst ι (r.body.produce[j]'insideP) = obj (subst ι t)
        rw [same, subst_obj]
      · have old : o ∈ s.present := by
          rcases mem_fire.mp present with ⟨inside, -⟩ | fresh
          · exact inside
          · exact absurd (by simpa [Selection.commit, objFiring] using fresh) made
        obtain ⟨t, same⟩ := gated.dataRows o old
        refine ⟨subst var t, ?_⟩
        rw [Firing.result_label_other _ made]
        show subst var (s.label o) = _
        rw [same, subst_obj]

/-- **Forward**: every admitted firing of the fixed program at `s` is matched by an admitted firing of
the stored-rule program at a gated `w`, and the results are gated. -/
theorem gated_forward {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)} (gated : Gated P s w)
    (f : Firing O Ext P.program s.frame) (admitted : f.Admits X s) :
    ∃ g : Firing (O ⊕ Fin P.rules.length) Ext (Stored DataFragment) w.frame, g.Admits X w ∧
      Gated P (f.result X s) (g.result X w) := by
  obtain ⟨r, member, ext, ι, sel, seen⟩ := f
  obtain ⟨k, coded⟩ := List.mem_iff_get.mp member
  have admitted' : (objFiring member s.frame ι sel seen).Admits X s := admitted
  have pair := gated_pair gated member coded sel seen admitted'.1.1
  exact ⟨_, pair.1.mpr admitted', pair.2 admitted'⟩

omit [DecidableEq O] in
/-- Claimed sets that are the matches of data patterns, moved along `inl`, are lifted sets. -/
theorem eq_liftSeen {K : Type*} {F : Expr → Finset (O ⊕ K)} {G : Expr → Finset O} :
    ∀ {ps : List Expr} {seen : List (Finset (O ⊕ K))},
      (∀ p ∈ ps, F p = (G p).map Function.Embedding.inl) → ps.length = seen.length →
        (∀ q ∈ ps.zip seen, F q.1 = q.2) → seen = liftSeen (ps.map G)
  | [], [], _, _, _ => rfl
  | p :: ps, A :: seen, same, lengths, claimed => by
      have head : F p = A := claimed (p, A) List.mem_cons_self
      have tail := eq_liftSeen (fun p' inside => same p' (List.mem_cons_of_mem _ inside))
        (Nat.succ.inj lengths) fun q inside => claimed q (List.mem_cons_of_mem _ inside)
      rw [tail, ← head, same p List.mem_cons_self]
      rfl
  | [], _ :: _, _, lengths, _ => absurd lengths (by simp)
  | _ :: _, [], _, lengths, _ => absurd lengths (by simp)

/-- **Backward**: every admitted firing of the stored-rule program at a gated `w` is the image of an
admitted firing of the fixed program at `s`, and the results are gated. -/
theorem gated_backward {s : State Tm O} {w : State Tm (O ⊕ Fin P.rules.length)} (gated : Gated P s w)
    (g : Firing (O ⊕ Fin P.rules.length) Ext (Stored DataFragment) w.frame) (admitted : g.Admits X w) :
    ∃ f : Firing O Ext P.program s.frame, f.Admits X s ∧ Gated P (f.result X s) (g.result X w) := by
  obtain ⟨r', hr', hg⟩ := stored_cases g
  rw [hg] at admitted ⊢
  generalize g.opening = ι at admitted ⊢
  generalize g.selection = sel' at admitted ⊢
  generalize g.seen = seen' at admitted ⊢
  obtain ⟨⟨freshW, -, -, takeLength, readLength, produceLength, collectLength⟩, enabled, ⟨_, τ₀, solved⟩,
    asks⟩ := id admitted
  have frag' := hr'.1
  have readLength' : r'.body.read.length + 1 = sel'.read.length := readLength
  obtain ⟨c₀, rest, reads, restLength⟩ := exists_cons_of_length readLength'
  have present := present_of_enabled enabled
  obtain ⟨-, takesF, readsF, -⟩ := (models_information (storedFiring hr' w.frame ι sel' seen')
    takeLength readLength τ₀).mp solved
  -- the first read is a code row of `P`
  have readsF' : List.Forall₂ (fun p o => nf (subst τ₀ (subst ι p)) = nf (subst τ₀ (w.label o)))
      (ruleCode r' :: r'.body.read) (c₀ :: rest) := by
    rw [← reads]
    exact readsF
  have codeRead := (List.forall₂_cons.mp readsF').1
  rw [subst_ruleCode frag', subst_ruleCode frag', nf_ruleCode frag'] at codeRead
  have c₀present : c₀ ∈ w.present := present c₀ (List.mem_append_right _ (reads ▸ List.mem_cons_self))
  obtain ⟨k, rfl⟩ : ∃ k, c₀ = .inr k := by
    cases c₀ with
    | inl o =>
        exfalso
        obtain ⟨t, same⟩ := gated.dataRows o ((mem_present_inl gated o).mp c₀present)
        rw [gated.data, same, subst_obj, nf_obj] at codeRead
        exact obj_ne_code _ _ codeRead.symm
    | inr k => exact ⟨k, rfl⟩
  rw [gated.codes, subst_ruleCode (P.data _ (List.get_mem _ _)).1,
    nf_ruleCode (P.data _ (List.get_mem _ _)).1] at codeRead
  have coded : P.rules.get k = r' := (ruleCode_injective codeRead).symm
  have member : r' ∈ P.program := coded ▸ List.get_mem _ _
  have addressed := P.addressed r' member
  -- takes and reads are data rows, made identities are fresh hence data identities
  have dataRow : ∀ {p : Expr} {x : O ⊕ Fin P.rules.length}, (∃ t, p = obj t) →
      nf (subst τ₀ (subst ι p)) = nf (subst τ₀ (w.label x)) → ∃ o, x = .inl o := by
    intro p x ⟨t, isData⟩ equated
    cases x with
    | inl o => exact ⟨o, rfl⟩
    | inr j =>
        exfalso
        rw [gated.codes, isData] at equated
        exact data_ne_code τ₀ ι (P.data _ (List.get_mem _ _)).1 equated
  obtain ⟨taken, takenEq⟩ := exists_map_inl (l := sel'.taken) fun x inside => by
    obtain ⟨i, below, rfl⟩ := List.mem_iff_getElem.mp inside
    exact dataRow (addressed.take _ (List.getElem_mem (takeLength ▸ below)))
      (index_of_forall₂ takesF i (takeLength ▸ below) below)
  have restF := (List.forall₂_cons.mp readsF').2
  obtain ⟨read, readEq⟩ := exists_map_inl (l := rest) fun x inside => by
    obtain ⟨i, below, rfl⟩ := List.mem_iff_getElem.mp inside
    exact dataRow (addressed.read _ (List.getElem_mem (restLength ▸ below)))
      (index_of_forall₂ restF i (restLength ▸ below) below)
  obtain ⟨made, madeEq⟩ := exists_map_inl (l := sel'.made) fun x inside => by
    cases x with
    | inl o => exact ⟨o, rfl⟩
    | inr j =>
        exfalso
        have freshMade : Disjoint (sel'.commit (T := Unit)).made w.present := enabled.fresh
        exact Finset.disjoint_left.mp freshMade (by simpa [Selection.commit] using inside)
          (mem_present_inr gated j)
  have selEq : sel' = lift k ⟨taken, read, made⟩ := by
    cases sel'
    simp only [lift, Selection.mk.injEq] at takenEq readEq madeEq reads ⊢
    exact ⟨takenEq, by rw [reads, readEq], madeEq⟩
  -- collect patterns are data rows: at a solution, each claimed set is the matches moved along `inl`
  obtain ⟨seen₀, seenEq⟩ : ∃ seen₀ : List (Finset O), seen' = liftSeen seen₀ := by
    have holdsW := (holds_iff_full (storedFiring hr' w.frame ι sel' seen') τ₀).mp
      (asks PUnit.unit τ₀ solved)
    refine ⟨_, eq_liftSeen (F := matchesAt X (b := PUnit.unit) τ₀ w.label w.present)
      (G := matchesAt X (b := PUnit.unit) τ₀ s.label s.present) (ps := r'.collect.map (subst ι)) ?_ ?_ ?_⟩
    · intro p inside
      obtain ⟨p₀, member₀, rfl⟩ := List.mem_map.mp inside
      obtain ⟨t, isData⟩ := addressed.collect p₀ member₀
      exact matchesAt_gated gated isData ι τ₀
    · rw [List.length_map]
      exact collectLength
    · have claimed := holdsW.2
      rw [row_eq] at claimed
      exact claimed
  subst selEq seenEq coded
  have freshS := fresh_from_codes gated hr' freshW member ⟨taken, read, made⟩ seen₀
  have pair := gated_pair gated member rfl ⟨taken, read, made⟩ seen₀ freshS
  exact ⟨_, pair.1.mp admitted, pair.2 (pair.1.mp admitted)⟩

end Steps

/-! ## The interpreter runs a fixed program held in the store -/

section Interpreter

variable {P : FixedProgram}

/-- **The representation of a store of the fixed program by a store of the interpreter**: a gated
store of the stored-rule program, represented by the interpreter's store. -/
def Runs (P : FixedProgram) (s : State Tm O) (u : State Tm (O ⊕ Fin P.rules.length)) : Prop :=
  ∃ w, Gated P s w ∧ Represents DataFragment w u

/-- **It starts at the store with codes.** -/
theorem fixed_program_start {s : State Tm O} (dataRows : ∀ o ∈ s.present, ∃ t, s.label o = obj t) :
    Runs P s (withCodes P s) :=
  ⟨withCodes P s, withCodes_gated P dataRows, represents_refl (gated_tagged (withCodes_gated P dataRows))⟩

/-- **The step of the interpreter from the store with codes and the step of the fixed program are
strongly bisimilar.** -/
theorem fixed_program_bisimulation {s : State Tm O} {u : State Tm (O ⊕ Fin P.rules.length)}
    (related : Runs P s u) :
    (∀ s', Succ (step X O Ext P.program).toStep s s' → ∃ u', InterpSucc u u' ∧ Runs P s' u') ∧
      (∀ u', InterpSucc u u' → ∃ s', Succ (step X O Ext P.program).toStep s s' ∧ Runs P s' u') := by
  obtain ⟨w, gated, rep⟩ := related
  constructor
  · rintro s' ⟨f, admitted, rfl⟩
    obtain ⟨g, admittedG, gated'⟩ := gated_forward gated f admitted
    obtain ⟨u', moved, rep'⟩ := (bisimulation dataFragment_closed rep).1 _ ⟨g, admittedG, rfl⟩
    exact ⟨u', moved, g.result X w, gated', rep'⟩
  · rintro u' ⟨g, admitted, rfl⟩
    obtain ⟨w', ⟨f', admittedF, rfl⟩, rep'⟩ := (bisimulation dataFragment_closed rep).2 _ ⟨g, admitted, rfl⟩
    obtain ⟨f, admittedP, gated'⟩ := gated_backward gated f' admittedF
    exact ⟨f.result X s, ⟨f, admittedP, rfl⟩, f'.result X w, gated', rep'⟩

/-- **Runs, step for step, in both directions.** -/
theorem fixed_program_runs {s : State Tm O} {u : State Tm (O ⊕ Fin P.rules.length)} (related : Runs P s u) :
    (∀ s', Relation.ReflTransGen (Succ (step X O Ext P.program).toStep) s s' →
      ∃ u', Relation.ReflTransGen InterpSucc u u' ∧ Runs P s' u') ∧
      (∀ u', Relation.ReflTransGen InterpSucc u u' →
        ∃ s', Relation.ReflTransGen (Succ (step X O Ext P.program).toStep) s s' ∧ Runs P s' u') := by
  constructor
  · intro s' run
    induction run with
    | refl => exact ⟨u, Relation.ReflTransGen.refl, related⟩
    | tail _ moved ih =>
        obtain ⟨u₁, runU, related₁⟩ := ih
        obtain ⟨u₂, movedU, related₂⟩ := (fixed_program_bisimulation related₁).1 _ moved
        exact ⟨u₂, runU.tail movedU, related₂⟩
  · intro u' run
    induction run with
    | refl => exact ⟨s, Relation.ReflTransGen.refl, related⟩
    | tail _ moved ih =>
        obtain ⟨s₁, runS, related₁⟩ := ih
        obtain ⟨s₂, movedS, related₂⟩ := (fixed_program_bisimulation related₁).2 _ moved
        exact ⟨s₂, runS.tail movedS, related₂⟩

end Interpreter

/-! ## A fixed program run through the interpreter -/

section Demo

open Examples (first second first_mem second_mem tok key five done)

theorem first_addressed : DataAddressed Examples.first :=
  ⟨by simp [Examples.first], by simp [Examples.first], by simp [Examples.first, kindOf],
    by simp [Examples.first]⟩

theorem second_addressed : DataAddressed Examples.second :=
  ⟨by simp [Examples.second], by simp [Examples.second], by simp [Examples.second, kindOf],
    by simp [Examples.second]⟩

/-- **The two-rule program, fixed.** -/
def demoProgram : FixedProgram where
  rules := [first, second]
  data r inside := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact first_mem
    · exact second_mem
  addressed r inside := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact first_addressed
    · exact second_addressed

/-- The labels of a store of data rows only: a token valued by the store's unknown, and the key five. -/
def dataLabel (o : ℕ) : Expr := if o = 0 then obj (tok (var 0)) else obj (key five)

/-- **A store of data rows only.** -/
def dataStart : State Tm ℕ := ⟨PUnit.unit, [], {0, 1}, dataLabel⟩

theorem dataStart_rows : ∀ o ∈ dataStart.present, ∃ t, dataStart.label o = obj t := by
  intro o present
  simp only [dataStart, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- `first` as a rule of the fixed program. -/
def demoFirst : Firing ℕ Ext demoProgram.program dataStart.frame :=
  ⟨first, by simp [FixedProgram.program, demoProgram], PUnit.unit, shift 10, ⟨[0], [1], [4]⟩, []⟩

theorem demoFirst_information :
    demoFirst.information X dataStart =
      [(obj (tok (var 10)), obj (tok (var 0))), (obj (key (var 11)), obj (key five)), (var 10, var 11)] := rfl

theorem demoFirst_admitted : demoFirst.Admits X dataStart := by
  refine ⟨⟨fresh_shift demoFirst rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [demoFirst_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [demoFirst_information] at solved
    refine (holds_iff demoFirst rfl σ).mpr ?_
    intro c inside
    simp only [demoFirst, first, List.mem_singleton] at inside
    subst inside
    have keyed : nf (subst σ (obj (key (var 11)))) = nf (subst σ (obj (key five))) :=
      solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [obj, key, five, subst, nf, Expr.cell.injEq, true_and] at keyed
    show nf (σ 11) = nf (subst σ five)
    exact keyed

/-- The store after `first`. -/
def dataMiddle : State Tm ℕ := demoFirst.result X dataStart

theorem dataMiddle_present : dataMiddle.present = {1, 4} := by decide

/-- `second` as a rule of the fixed program, on the row `first` made. -/
def demoSecond : Firing ℕ Ext demoProgram.program dataMiddle.frame :=
  ⟨second, by simp [FixedProgram.program, demoProgram], PUnit.unit, shift 20, ⟨[4], [], [5]⟩, []⟩

theorem demoSecond_information :
    demoSecond.information X dataMiddle =
      [(obj (tok (var 10)), obj (tok (var 0))), (obj (key (var 11)), obj (key five)), (var 10, var 11),
        (obj (Examples.seen (var 20)), obj (Examples.seen (var 10)))] := rfl

theorem demoSecond_admitted : demoSecond.Admits X dataMiddle := by
  refine ⟨⟨fresh_shift demoSecond rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, ?_⟩, ?_⟩
  · rw [demoSecond_information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl <;> rfl
  · intro b σ solved
    rw [demoSecond_information] at solved
    refine (holds_iff demoSecond rfl σ).mpr ?_
    intro c inside
    simp only [demoSecond, second, List.mem_singleton] at inside
    subst inside
    have keyed : nf (subst σ (obj (key (var 11)))) = nf (subst σ (obj (key five))) :=
      solved _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have told : nf (subst σ (var 10)) = nf (subst σ (var 11)) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have seenRow : nf (subst σ (obj (Examples.seen (var 20)))) = nf (subst σ (obj (Examples.seen (var 10)))) :=
      solved _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    simp only [obj, key, Examples.seen, five, subst, nf, Expr.cell.injEq, true_and] at keyed told seenRow
    show nf (σ 20) = nf (subst σ five)
    rw [seenRow, told, keyed]
    rfl

/-- **A run of length two of the fixed program from a store of data rows.** -/
theorem demo_run :
    Succ (step X ℕ Ext demoProgram.program).toStep dataStart dataMiddle ∧
      Succ (step X ℕ Ext demoProgram.program).toStep dataMiddle (demoSecond.result X dataMiddle) :=
  ⟨⟨demoFirst, demoFirst_admitted, rfl⟩, ⟨demoSecond, demoSecond_admitted, rfl⟩⟩

/-- **The same run through the interpreter**, from the store holding the data rows and the codes of the
two rules: two admitted firings of `U`. -/
theorem demo_interpreter_run :
    ∃ u₁ u₂, InterpSucc (withCodes demoProgram dataStart) u₁ ∧ InterpSucc u₁ u₂ ∧
      Runs demoProgram (demoSecond.result X dataMiddle) u₂ := by
  have start := fixed_program_start (P := demoProgram) dataStart_rows
  obtain ⟨u₁, moved₁, related₁⟩ := (fixed_program_bisimulation start).1 _ demo_run.1
  obtain ⟨u₂, moved₂, related₂⟩ := (fixed_program_bisimulation related₁).1 _ demo_run.2
  exact ⟨u₁, u₂, moved₁, moved₂, related₂⟩

/-! ### A collect pattern -/

/-- **A rule with a collect pattern**: take a token, see the rows `obj (key five)`, make a seen row. -/
def tally : Rule Tm :=
  ⟨PUnit.unit, ⟨[obj (tok (var 0))], [], [], [], [obj (Examples.seen (var 0))]⟩, [obj (key five)]⟩

theorem tally_mem : tally ∈ DataFragment := by
  refine ⟨Examples.fragment_of_check rfl, ?_⟩
  intro m inside
  simp only [tally, List.mem_singleton] at inside
  exact ⟨_, inside⟩

theorem tally_addressed : DataAddressed tally :=
  ⟨by simp [tally], by simp [tally], by simp [tally], by simp [tally]⟩

/-- The program of `tally`, fixed. -/
def tallyProgram : FixedProgram where
  rules := [tally]
  data r inside := by
    simp only [List.mem_singleton] at inside
    subst inside
    exact tally_mem
  addressed r inside := by
    simp only [List.mem_singleton] at inside
    subst inside
    exact tally_addressed

/-- `tally` at the store of data rows, claiming the key row `1`. -/
def tallyFiring (claimed : Finset ℕ) : Firing ℕ Ext tallyProgram.program dataStart.frame :=
  ⟨tally, by simp [FixedProgram.program, tallyProgram], PUnit.unit, shift 10, ⟨[0], [], [4]⟩, [claimed]⟩

theorem tallyFiring_information (claimed : Finset ℕ) :
    (tallyFiring claimed).information X dataStart = [(obj (tok (var 10)), obj (tok (var 0)))] := rfl

theorem tally_solved (claimed : Finset ℕ) :
    action.Models (fun _ => five) ((tallyFiring claimed).information X dataStart) := by
  rw [tallyFiring_information]
  intro e inside
  simp only [List.mem_singleton] at inside
  subst inside
  rfl

/-- **`tally` fires claiming exactly the key row.** -/
theorem tally_admitted : (tallyFiring {1}).Admits X dataStart := by
  refine ⟨⟨fresh_shift (tallyFiring {1}) rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => five, tally_solved {1}⟩, ?_⟩
  intro b σ _
  refine (holds_iff_full (tallyFiring {1}) σ).mpr
    ⟨fun c inside => by simp [tallyFiring, tally] at inside, fun q inside => ?_⟩
  have isQ := List.mem_singleton.mp inside
  subst isQ
  rw [row_eq]
  ext o
  rw [mem_matchesAt]
  show o ∈ ({0, 1} : Finset ℕ) ∧ nf (subst σ (obj (key five))) = nf (subst σ (dataLabel o)) ↔
    o ∈ ({1} : Finset ℕ)
  constructor
  · rintro ⟨present, equated⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at present ⊢
    rcases present with rfl | rfl
    · exfalso
      simp [dataLabel, obj, key, tok, five, subst, nf] at equated
    · rfl
  · intro one
    simp only [Finset.mem_singleton] at one
    subst one
    exact ⟨by decide, rfl⟩

/-- **The collect pattern through the interpreter**, from the store holding the data rows and the code of
`tally`. -/
theorem tally_interpreter_run :
    ∃ u, InterpSucc (withCodes tallyProgram dataStart) u ∧
      Runs tallyProgram ((tallyFiring {1}).result X dataStart) u :=
  (fixed_program_bisimulation (fixed_program_start (P := tallyProgram) dataStart_rows)).1 _
    ⟨tallyFiring {1}, tally_admitted, rfl⟩

/-- **A wrong claimed set is refused**: the key row matches the collect pattern. -/
theorem tally_wrong_refused : ¬ (tallyFiring ∅).Admits X dataStart := by
  rintro ⟨-, -, -, asks⟩
  have holds := (holds_iff_full (tallyFiring ∅) (fun _ => five)).mp (asks PUnit.unit _ (tally_solved ∅))
  have claimed : matchesAt X (b := PUnit.unit) (fun _ => five) ((tallyFiring ∅).row X dataStart)
      dataStart.present (obj (key five)) = ∅ :=
    holds.2 (obj (key five), ∅) (List.mem_singleton_self _)
  rw [row_eq] at claimed
  have one : (1 : ℕ) ∈ matchesAt X (b := PUnit.unit) (fun _ => five) dataStart.label dataStart.present
      (obj (key five)) := by
    rw [mem_matchesAt]
    exact ⟨by decide, rfl⟩
  rw [claimed] at one
  exact Finset.notMem_empty 1 one

end Demo

/-! ## Composition -/

/-- **The stored-rule program of a union is the union of the stored-rule programs.** -/
theorem stored_union (F G : Set (Rule Tm)) : Stored (F ∪ G) = Stored F ∪ Stored G := by
  ext q
  constructor
  · rintro ⟨r, member | member, rfl⟩
    · exact Or.inl ⟨r, member, rfl⟩
    · exact Or.inr ⟨r, member, rfl⟩
  · rintro (⟨r, member, rfl⟩ | ⟨r, member, rfl⟩)
    · exact ⟨r, Or.inl member, rfl⟩
    · exact ⟨r, Or.inr member, rfl⟩

/-- **A union of fragments closed under what they make is closed.** -/
theorem closedFragment_union {F G : Set (Rule Tm)} (closedF : ClosedFragment F)
    (closedG : ClosedFragment G) : ClosedFragment (F ∪ G) :=
  ⟨fun r inside => inside.elim (closedF.fragment r) (closedG.fragment r), fun r inside m made =>
    inside.elim
      (fun inF => (closedF.made r inF m made).imp id fun ⟨r', hr', same⟩ => ⟨r', Or.inl hr', same⟩)
      (fun inG => (closedG.made r inG m made).imp id fun ⟨r', hr', same⟩ => ⟨r', Or.inr hr', same⟩)⟩

/-! ## Why the patterns of a fixed program must be data rows -/

section Control

/-- **A rule reading any row**, by the pattern `var 0`. -/
def readAny : Rule Tm := ⟨PUnit.unit, ⟨[], [var 0], [], [], [obj Examples.done]⟩, []⟩

theorem readAny_mem : readAny ∈ DataFragment :=
  ⟨Examples.fragment_of_check rfl, fun m inside => by
    simp only [readAny, List.mem_singleton] at inside
    exact ⟨_, inside⟩⟩

theorem readAny_not_addressed : ¬ DataAddressed readAny := by
  intro addressed
  obtain ⟨t, same⟩ := addressed.read (var 0) (by simp [readAny])
  exact Expr.noConfusion same

/-- A store holding only the code of `readAny`. -/
def codeOnly : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => ruleCode readAny⟩

/-- The empty store. -/
def emptyStore : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => nil⟩

/-- `readAny`, gated by its code at row `0`, reading row `0` again as `var 0`. -/
def readAnyFiring : Firing ℕ Ext (Stored DataFragment) codeOnly.frame :=
  storedFiring readAny_mem codeOnly.frame (shift 10) ⟨[], [0, 0], [1]⟩ []

/-- **With its code in the store, `readAny` reads its own code row**: the pattern `var 0` is a fresh
unknown, which the code row binds. -/
theorem readAny_reads_code : readAnyFiring.Admits X codeOnly := by
  have information : readAnyFiring.information X codeOnly =
      [(ruleCode readAny, ruleCode readAny), (var 10, ruleCode readAny)] := by decide
  refine ⟨⟨fresh_shift readAnyFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, fun _ => ruleCode readAny, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · rfl
    · show nf (ruleCode readAny) = nf (subst _ (ruleCode readAny))
      rw [subst_ruleCode readAny_mem.1]
  · intro b σ _
    refine (holds_iff readAnyFiring rfl σ).mpr ?_
    intro c inside
    simp [readAnyFiring, storedFiring, stored, readAny] at inside

/-- **Without the code, the fixed program `{readAny}` has no firing at the empty store**: it has a read
and nothing to read. -/
theorem readAny_idle_without_codes (f : Firing ℕ Ext ({readAny} : Program Tm) emptyStore.frame) :
    ¬ f.Admits X emptyStore := by
  rintro ⟨⟨-, -, -, -, readLength, -, -⟩, enabled, -, -⟩
  have isReadAny : f.rule = readAny := f.member
  have lengths : 1 = f.selection.read.length := by
    have := readLength
    rw [isReadAny] at this
    simpa [readAny] using this
  obtain ⟨c, rest, reads, -⟩ := exists_cons_of_length (show 0 + 1 = f.selection.read.length from lengths)
  have read := enabled.kept_subset (show c ∈ (f.selection.commit (T := Unit)).kept by
    simp [Selection.commit, reads])
  simp [emptyStore] at read

/-- **A rule asking that no row at all be present**, by the none pattern `var 0`. -/
def noRow : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (var 0)], [obj Examples.done]⟩, []⟩

theorem noRow_mem : noRow ∈ DataFragment :=
  ⟨Examples.fragment_of_check rfl, fun m inside => by
    simp only [noRow, List.mem_singleton] at inside
    exact ⟨_, inside⟩⟩

theorem noRow_not_addressed : ¬ DataAddressed noRow := by
  intro addressed
  obtain ⟨t, same⟩ := addressed.query (.predicate .none (var 0)) (by simp [noRow]) (by simp [kindOf])
  exact Expr.noConfusion same

/-- `noRow` as the fixed program `{noRow}`, at the empty store. -/
def noRowFiring : Firing ℕ Ext ({noRow} : Program Tm) emptyStore.frame :=
  ⟨noRow, Set.mem_singleton _, PUnit.unit, shift 10, ⟨[], [], [0]⟩, []⟩

/-- **The fixed program `{noRow}` fires at the empty store.** -/
theorem noRow_fires : noRowFiring.Admits X emptyStore := by
  have information : noRowFiring.information X emptyStore = [] := rfl
  refine ⟨⟨fresh_shift noRowFiring rfl (by decide), by decide, by decide, rfl, rfl, rfl, rfl⟩,
    by decide, ⟨PUnit.unit, var, ?_⟩, ?_⟩
  · rw [information]
    intro e inside
    simp at inside
  · intro b σ _
    refine (holds_iff noRowFiring rfl σ).mpr ?_
    intro c inside
    simp only [noRowFiring, noRow, List.mem_singleton] at inside
    subst inside
    intro o present
    exact absurd present (Finset.notMem_empty o)

/-- A store holding only the code of `noRow`: the empty store with its code. -/
def noRowCodeOnly : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => ruleCode noRow⟩

theorem noRowCodeOnly_tagged : Tagged DataFragment noRowCodeOnly :=
  fun _ _ => Or.inr ⟨noRow, noRow_mem, rfl⟩

/-- **With its code in the store, `noRow` never fires**, whatever its opening: freshness gives a
solution sending its none pattern to the code row. -/
theorem noRow_refused_with_code (f : Firing ℕ Ext (Stored DataFragment) noRowCodeOnly.frame)
    (isNoRow : f.rule = stored noRow) : ¬ f.Admits X noRowCodeOnly := by
  obtain ⟨rule, member, ext, ι, sel, seen⟩ := f
  subst isNoRow
  rintro ⟨⟨fresh, -, -, takeLength, readLength, -, -⟩, -, -, asks⟩
  have frag := noRow_mem.1
  have takenNil : sel.taken = [] := List.length_eq_zero_iff.mp (takeLength : 0 = sel.taken.length).symm
  have readLength' : 0 + 1 = sel.read.length := readLength
  obtain ⟨c₀, rest, reads, restLength⟩ := exists_cons_of_length readLength'
  have restNil : rest = [] := List.length_eq_zero_iff.mp restLength.symm
  subst restNil
  obtain ⟨u, -, onRule⟩ := fresh PUnit.unit var (fun _ => ruleCode noRow)
  have solvedU : X.Models (a := noRowCodeOnly.frame) (b := PUnit.unit) u
      ((⟨stored noRow, member, ext, ι, sel, seen⟩ :
        Firing ℕ Ext (Stored DataFragment) noRowCodeOnly.frame).information X noRowCodeOnly) := by
    refine (models_information _ takeLength readLength u).mpr ⟨by simp [noRowCodeOnly], ?_, ?_, ?_⟩
    · show List.Forall₂ _ ([] : List Expr) sel.taken
      rw [takenNil]
      exact List.Forall₂.nil
    · show List.Forall₂ (fun p o => nf (subst u (subst ι p)) = nf (subst u (noRowCodeOnly.label o)))
        [ruleCode noRow] sel.read
      rw [reads]
      refine List.Forall₂.cons ?_ List.Forall₂.nil
      show nf (subst u (subst ι (ruleCode noRow))) = nf (subst u (ruleCode noRow))
      rw [subst_ruleCode frag]
    · intro e inside
      simp [stored, noRow] at inside
  have holds := (holds_iff _ rfl u).mp (asks PUnit.unit u solvedU) (.predicate .none (var 0))
    (by simp [stored, noRow])
  have pattern : nf (subst u (subst ι (var 0))) = nf (subst (fun _ => ruleCode noRow) (var 0)) :=
    onRule (var 0) (by simp [Rule.terms, stored, noRow, checkTerms])
  refine holds 0 (by simp [noRowCodeOnly]) ?_
  show nf (subst u (subst ι (var 0))) = nf (subst u (Firing.row X noRowCodeOnly _ 0))
  rw [row_eq, pattern]
  show nf (ruleCode noRow) = nf (subst u (ruleCode noRow))
  rw [subst_ruleCode frag]

/-- **So the interpreter does nothing from the empty store with the code of `noRow`**, where the
fixed program `{noRow}` fires from the empty store (`noRow_fires`): a none pattern that is not
a data row sees the code rows. -/
theorem noRow_interpreter_idle (g : Firing ℕ Ext U noRowCodeOnly.frame) :
    ¬ g.Admits X noRowCodeOnly := by
  intro admitted
  obtain ⟨f, admittedF, -, -⟩ := backward dataFragment_closed (represents_refl noRowCodeOnly_tagged) g admitted
  obtain ⟨r, hr, hf⟩ := stored_cases f
  have admittedF' := admittedF
  rw [hf] at admittedF'
  obtain ⟨c₀, -, coded⟩ := Examples.code_present dataFragment_closed noRowCodeOnly_tagged hr admittedF'
  have sameRule : noRow = r := ruleCode_injective coded
  subst sameRule
  exact noRow_refused_with_code f (by rw [hf]; rfl) admittedF

end Control

#print axioms demo_run
#print axioms demo_interpreter_run
#print axioms stored_union
#print axioms closedFragment_union
#print axioms readAny_not_addressed
#print axioms readAny_reads_code
#print axioms readAny_idle_without_codes
#print axioms gated_pair
#print axioms gated_forward
#print axioms gated_backward
#print axioms fixed_program_start
#print axioms fixed_program_bisimulation
#print axioms fixed_program_runs
#print axioms withCodes_gated
#print axioms gated_tagged
#print axioms gated_models
#print axioms fresh_to_codes
#print axioms fresh_from_codes
#print axioms knowledge_gated
#print axioms holds_gated
#print axioms matchesAt_gated
#print axioms collect_gated
#print axioms eq_liftSeen
#print axioms tally_admitted
#print axioms tally_interpreter_run
#print axioms tally_wrong_refused
#print axioms noRow_not_addressed
#print axioms noRow_fires
#print axioms noRow_refused_with_code
#print axioms noRow_interpreter_idle

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Gating
