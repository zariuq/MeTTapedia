import Mettapedia.Languages.MeTTa.PeTTa.LibTransformAdmission

/-!
# `absent` is a check of the step

The model evaluates `(absent p)` by matching: the condition holds when no stored atom
matches `p` under the row's bindings. The step states absence as a check
(`Check.absent`), which must hold at **every** solution of the firing's equations: no
present label is equal to the pattern under that solution. This module proves that the
model's condition gives the step's check, for a kernel of reads and takes followed by
`absent` conditions of single patterns, on a ground store.

* `Agrees`: a solution gives every variable a list of bindings binds its bound value.
* `rel_agrees`: a match that a solution solves keeps the solution in agreement with the
  bindings it produces.
* `rel_of_solution`: a pattern matches its own instance under any solution that agrees with
  the bindings so far (completeness of one-way matching against solutions).
* `walk_kernel_agrees`: every solution of a kernel row's equations agrees with the row's
  bindings. So the row's bindings are the common part of all solutions, and the variables
  they leave free are free in the equations too.
* `absent_check_holds`: where no stored atom matches `p` under bindings a solution agrees
  with, no present label equals `p` under that solution.
* `guarded_selection_valid`, `guarded_fire_admitted`: a firing of a kernel of reads and
  takes guarded by absences is admitted by the first-order step for the rule instance
  whose takes and reads are the patterns and whose checks are the absences
  (`guardedRule`), at the configuration with the rows' occurrences and no knowledge.
* `guided_guarded`, `guarded_branch_fire_admitted`, `guarded_transform_admitted_run`: the
  same for a branch (its absences are evaluated again when it fires, against the store as
  it is then) and for a whole call: a run over the proposals in which every branch that
  fires is admitted with its absences as checks.

Negative example: `Controls.absent_refuses_when_present` (with a stored atom matching the
absent pattern the kernel row is dropped, so nothing fires).

Scope: `absent` of one pattern. A joint absence `(absent (, p q))` is a
query over joint matches and is not a `Check.absent`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst matchAtom isGroundAtom MatchAtomRel matchAtom_sound matchAtom_complete)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction Check)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns (Firing)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (publish)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## Solutions and bindings -/

/-- A solution agrees with a list of bindings when it gives every bound variable its bound
value. -/
def Agrees (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (σ : Subst) : Prop :=
  ∀ v a, Subst.lookup σ v = some a → SubstitutionAlgebra.subst ρ (.var v) = a

theorem agrees_nil (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) : Agrees ρ [] := by
  intro v a found
  simp [Subst.lookup] at found

/-- Looking up in bindings with one more binding in front. -/
theorem lookup_cons (v w : String) (b : Atom) (σ : Subst) :
    Subst.lookup ((v, b) :: σ) w = if v = w then some b else Subst.lookup σ w := by
  by_cases same : v = w
  · subst same
    simp [Subst.lookup]
  · simp [Subst.lookup, same]

/-- **A match a solution solves keeps the solution in agreement.** -/
theorem rel_agrees {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst}
    {σ τ : Subst} {p b : Atom} (rel : MatchAtomRel σ p b τ) :
    Agrees ρ σ → SubstitutionAlgebra.subst ρ p = b → Agrees ρ τ := by
  induction rel with
  | var_fresh _ =>
      intro agrees solved w a found
      rw [lookup_cons] at found
      split at found
      · next same =>
          subst same
          cases found
          exact solved
      · exact agrees w a found
  | var_bound _ => exact fun agrees _ => agrees
  | symbol => exact fun agrees _ => agrees
  | grounded => exact fun agrees _ => agrees
  | expr_nil => exact fun agrees _ => agrees
  | expr_cons _ _ headIH tailIH =>
      intro agrees solved
      simp only [SubstitutionAlgebra.subst, SubstitutionAlgebra.subst.substList,
        Atom.expression.injEq, List.cons.injEq] at solved
      refine tailIH (headIH agrees solved.1) ?_
      simp only [SubstitutionAlgebra.subst, solved.2]

/-- **A pattern matches its own instance** under a solution that agrees with the bindings
so far: one-way matching is complete against solutions. -/
theorem rel_of_solution (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) :
    ∀ (p : Atom) (σ : Subst), Agrees ρ σ →
      ∃ τ, MatchAtomRel σ p (SubstitutionAlgebra.subst ρ p) τ
  | .var v, σ, agrees => by
      cases found : Subst.lookup σ v with
      | none => exact ⟨_, .var_fresh found⟩
      | some a =>
          rw [agrees v a found]
          exact ⟨σ, .var_bound found⟩
  | .symbol _, σ, _ => ⟨σ, .symbol⟩
  | .grounded _, σ, _ => ⟨σ, .grounded⟩
  | .expression es, σ, agrees => by
      simp only [SubstitutionAlgebra.subst]
      exact list es σ agrees
where
  list : ∀ (es : List Atom) (σ : Subst), Agrees ρ σ →
      ∃ τ, MatchAtomRel σ (.expression es)
        (.expression (SubstitutionAlgebra.subst.substList ρ es)) τ
    | [], σ, _ => ⟨σ, .expr_nil⟩
    | e :: es, σ, agrees => by
        obtain ⟨σ', head⟩ := rel_of_solution ρ e σ agrees
        obtain ⟨σ'', tail⟩ := list es σ' (rel_agrees head agrees rfl)
        exact ⟨σ'', .expr_cons head tail⟩

/-- Every solution of a kernel row's equations agrees with the row's bindings. -/
theorem walk_kernel_agrees {s : Store} {firing : Bool}
    {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst} :
    ∀ (pats : Footprint) {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (kernelOf pats) → Agrees ρ σ →
      List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats w.2 → Agrees ρ w.1
  | [], σ, w, member, agrees, _ => by
      simp only [kernelOf, List.map_nil, walk, List.mem_singleton] at member
      subst member
      exact agrees
  | (m, p) :: pats, σ, w, member, agrees, solved => by
      obtain ⟨r, picked, v, later, rfl⟩ :=
        (mem_walk_pat (m := m) (p := p) (cs := kernelOf pats)).mp member
      obtain ⟨_, matched⟩ := mem_matchesIn.mp picked
      cases solved with
      | cons head rest =>
          exact walk_kernel_agrees pats (w := v) later
            (rel_agrees (matchAtom_sound matched) agrees head) rest

/-! ## The check -/

/-- **Where nothing matches, nothing is equal.** If no stored atom matches `p` under
bindings that the solution `ρ` agrees with, then no present label equals `p` under `ρ`:
the step's absence check holds at `ρ`. -/
theorem absent_check_holds {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {σ : Subst} {p : Atom} (none : matchesIn s σ p = [])
    {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst} (agrees : Agrees ρ σ) :
    (Check.absent p).Holds atomAction ρ label rows.toFinset := by
  intro o present equal
  have stored : label o ∈ s := by
    rw [← rep.labels]
    exact List.mem_map_of_mem (List.mem_toFinset.mp present)
  have fixed : SubstitutionAlgebra.subst ρ (label o) = label o :=
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
      (vars_of_ground _ (ground _ stored))
  have instance' : SubstitutionAlgebra.subst ρ p = label o := by
    have : SubstitutionAlgebra.subst ρ p = SubstitutionAlgebra.subst ρ (label o) := equal
    rw [this, fixed]
  obtain ⟨τ, rel⟩ := rel_of_solution ρ p σ agrees
  rw [instance'] at rel
  have found : (τ, label o) ∈ matchesIn s σ p :=
    mem_matchesIn.mpr ⟨stored, matchAtom_complete rel⟩
  rw [none] at found
  exact List.not_mem_nil found

/-! ## A kernel guarded by absences -/

/-- The conditions `(absent p)` for each pattern, in order. -/
def absentsOf (ps : List Atom) : List Conj := ps.map fun p => .absent (.one p)

/-- The rule instance of a kernel of reads and takes guarded by absences. -/
def guardedRule (pats : Footprint) (absents : List Atom) : RuleInstance Atom :=
  ⟨takes pats, reads pats, [], absents.map Check.absent, []⟩

/-- The rows of a list of absences: the bindings as they are and no footprint, when every
absence holds; none otherwise. -/
theorem mem_walk_absents {s : Store} {firing : Bool} :
    ∀ (ps : List Atom) {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (absentsOf ps) ↔ w = (σ, []) ∧ ∀ p ∈ ps, matchesIn s σ p = []
  | [], σ, w => by simp [absentsOf, walk]
  | p :: ps, σ, w => by
      have shape : absentsOf (p :: ps) = Conj.absent (.one p) :: absentsOf ps := rfl
      rw [shape, walk_absent_one]
      split
      · next holds =>
          rw [mem_walk_absents ps]
          simp [holds]
      · next fails =>
          simp [fails]

/-- From the takes and the reads back to the conjuncts, when the modes agree. -/
theorem forall₂_of_takes_reads {R : Atom → Atom → Prop} :
    ∀ {pats fp : Footprint}, pats.map Prod.fst = fp.map Prod.fst →
      List.Forall₂ R (takes pats) (takes fp) → List.Forall₂ R (reads pats) (reads fp) →
      List.Forall₂ (fun e f => R e.2 f.2) pats fp
  | [], [], _, _, _ => List.Forall₂.nil
  | [], _ :: _, modes, _, _ => by simp at modes
  | _ :: _, [], modes, _, _ => by simp at modes
  | (m, p) :: pats, (m', b) :: fp, modes, taken, read => by
      simp only [List.map_cons, List.cons.injEq] at modes
      obtain ⟨same, rest⟩ := modes
      subst same
      cases m with
      | read =>
          simp only [reads, List.filterMap_cons] at read
          simp only [takes, List.filterMap_cons] at taken
          cases read with
          | cons head tail =>
              exact List.Forall₂.cons head (forall₂_of_takes_reads rest taken tail)
      | take =>
          simp only [reads, List.filterMap_cons] at read
          simp only [takes, List.filterMap_cons] at taken
          cases taken with
          | cons head tail =>
              exact List.Forall₂.cons head (forall₂_of_takes_reads rest tail read)

/-- A relation on a list and the image of another, from the relation element by element,
where the second elements may be used as members. -/
theorem forall₂_map_of_mem {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop} {f : β → γ} :
    ∀ {l : List α} {u : List β}, List.Forall₂ S l u → (∀ a, ∀ b ∈ u, S a b → R a (f b)) →
      List.Forall₂ R l (u.map f)
  | _, _, .nil, _ => List.Forall₂.nil
  | _, _, .cons head tail, each =>
      List.Forall₂.cons (each _ _ (List.mem_cons_self ..) head)
        (forall₂_map_of_mem tail fun a b member => each a b (List.mem_cons_of_mem _ member))

/-- The core of the guarded admission: a footprint that solves the kernel's patterns under
the bindings `σ`, where every solution of those equations agrees with `σ` and no stored
atom matches an absent pattern under `σ`, realized by a selection, is valid for the guarded
rule instance. -/
theorem guarded_valid_of {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats fp : Footprint} {absents : List Atom} {σ : Subst}
    (solved : List.Forall₂
      (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution σ) (e.2, f.2)) pats fp)
    (agreesOf : ∀ ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst,
      List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats fp → Agrees ρ σ)
    (none : ∀ p ∈ absents, matchesIn s σ p = []) {sel : Selection O}
    (real : Realizes label rows fp sel) :
    sel.Valid atomAction label (guardedRule pats absents) ⟨[], rows.toFinset⟩ := by
  have plain := selection_valid_of_solved solved real
  have modes := forall₂_modes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
  refine ⟨plain.take_distinct, plain.output_distinct, plain.take_length, plain.read_length,
    plain.outputs, plain.occurrences, plain.consistent, ?_⟩
  intro check member ρ models
  obtain ⟨p, inside, rfl⟩ := List.mem_map.mp member
  have fixed : ∀ o ∈ rows, SubstitutionAlgebra.subst ρ (label o) = label o := fun o present =>
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
      (vars_of_ground _ (ground _ (by rw [← rep.labels]; exact List.mem_map_of_mem present)))
  have parts : atomAction.Models ρ
      (Selection.equations label (takes pats) sel.taken) ∧
      atomAction.Models ρ (Selection.equations label (reads pats) sel.read) := by
    have all : atomAction.Models ρ
        (sel.problem label (guardedRule pats absents) ⟨[], rows.toFinset⟩) := models
    simp only [Selection.problem, guardedRule, List.nil_append, List.append_nil,
      SubstitutionAction.models_append] at all
    exact all
  have takeSolved : List.Forall₂ (fun p b => SubstitutionAlgebra.subst ρ p = b)
      (takes pats) (takes fp) := by
    rw [← real.taken_labels]
    refine forall₂_map_of_mem
      ((Selection.models_equations_iff atomAction ρ label plain.take_length).mp parts.1) ?_
    intro a o member equal
    have : SubstitutionAlgebra.subst ρ a = SubstitutionAlgebra.subst ρ (label o) := equal
    rw [this, fixed o (real.taken_present o member)]
  have readSolved : List.Forall₂ (fun p b => SubstitutionAlgebra.subst ρ p = b)
      (reads pats) (reads fp) := by
    rw [← real.read_labels]
    refine forall₂_map_of_mem
      ((Selection.models_equations_iff atomAction ρ label plain.read_length).mp parts.2) ?_
    intro a o member equal
    have : SubstitutionAlgebra.subst ρ a = SubstitutionAlgebra.subst ρ (label o) := equal
    rw [this, fixed o (real.read_present o member)]
  exact absent_check_holds rep ground (none p inside)
    (agreesOf ρ (forall₂_of_takes_reads modes takeSolved readSolved))

/-- **A realized row of a guarded kernel is a valid selection of the step**, its absences
checks that hold at every solution of its equations. -/
theorem guarded_selection_valid {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {absents : List Atom} {firing : Bool} {k : Subst × Footprint}
    (walked : k ∈ walk s firing [] (kernelOf pats))
    (none : ∀ p ∈ absents, matchesIn s k.1 p = []) {sel : Selection O}
    (real : Realizes label rows k.2 sel) :
    sel.Valid atomAction label (guardedRule pats absents) ⟨[], rows.toFinset⟩ :=
  guarded_valid_of rep ground
    (walk_kernel_solves ground pats walked
      (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl k.1))
    (fun ρ solved => walk_kernel_agrees pats walked (agrees_nil ρ) solved) none real

/-- Without a guide the absences are fired as written. -/
theorem guided_absentsOf_nil : ∀ ps : List Atom, guided (absentsOf ps) [] = absentsOf ps
  | [] => rfl
  | p :: ps => by
      show Conj.absent (.one p) :: guided (absentsOf ps) [] = Conj.absent (.one p) :: absentsOf ps
      rw [guided_absentsOf_nil ps]

/-- Without a guide the guarded kernel is fired as written. -/
theorem guided_guarded_nil : ∀ (pats : Footprint) (absents : List Atom),
    guided (kernelOf pats ++ absentsOf absents) [] = kernelOf pats ++ absentsOf absents
  | [], absents => guided_absentsOf_nil absents
  | (m, p) :: pats, absents => by
      show Conj.pat m p :: guided (kernelOf pats ++ absentsOf absents) [] =
        Conj.pat m p :: (kernelOf pats ++ absentsOf absents)
      rw [guided_guarded_nil pats absents]

/-- **A firing of a kernel of reads and takes guarded by absences is admitted by the
first-order step**, for the rule instance whose checks are the absences. -/
theorem guarded_fire_admitted {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {absents : List Atom} {emit : Subst → Answers} {out : Answers}
    (fired : LibTransform.fire s [] ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit =
      some (s', out)) :
    ∃ (sel : Selection O) (rows' : List O),
      (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
          (guardedRule pats absents, sel)).Valid atomAction label ⟨[], rows.toFinset⟩ ∧
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' := by
  obtain ⟨c, member, sel, rows', real, _, same, rep', _, _⟩ := fire_publishes rep fired
  obtain ⟨w, walked, rfl⟩ := List.mem_map.mp member
  have unguided := guided_guarded_nil pats absents
  rw [unguided, List.append_nil, walk_append] at walked
  obtain ⟨k, kernelRow, inside⟩ := List.mem_flatMap.mp walked
  obtain ⟨v, absentRow, rfl⟩ := List.mem_map.mp inside
  obtain ⟨rfl, none⟩ := (mem_walk_absents absents).mp absentRow
  have footprint : (Candidate.footprint ⟨k.2 ++ [], [(k.1, [])]⟩) = k.2 := by
    simp [Candidate.footprint]
  rw [footprint] at real
  exact ⟨sel, rows', (Firing.valid_ofPlain_iff atomAction label _ _).mpr
    (guarded_selection_valid rep ground kernelRow none real), same, rep'⟩

/-! ## Branches of a guarded kernel, and a whole call -/

/-- A guided guarded kernel is the guided kernel followed by its absences: an absence is
evaluated again when the branch fires. -/
theorem guided_guarded : ∀ (pats g : Footprint) (absents : List Atom), Fits pats g →
    guided (kernelOf pats ++ absentsOf absents) g = guided (kernelOf pats) g ++ absentsOf absents
  | [], [], absents, _ => guided_absentsOf_nil absents
  | [], _ :: _, _, fits => by have := fits.modes; simp at this
  | _ :: _, [], _, fits => by have := fits.modes; simp at this
  | (m, p) :: pats, (use, a) :: g, absents, fits => by
      have rest : Fits pats g :=
        ⟨by have := fits.modes; simp only [List.map_cons, List.cons.injEq] at this; exact this.2,
          fun e inside => fits.ground e (List.mem_cons_of_mem _ inside)⟩
      show Conj.pat use a :: Conj.as p a :: guided (kernelOf pats ++ absentsOf absents) g =
        Conj.pat use a :: Conj.as p a :: (guided (kernelOf pats) g ++ absentsOf absents)
      rw [guided_guarded pats g absents rest]

/-- Every solution of a guided kernel row's equations agrees with the row's bindings. -/
theorem walk_guided_kernel_agrees {s : Store} {firing : Bool}
    {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst} :
    ∀ (pats g : Footprint), Fits pats g → ∀ {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (guided (kernelOf pats) g) → Agrees ρ σ →
      List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats g → Agrees ρ w.1
  | [], [], _, σ, w, member, agrees, _ => by
      simp only [kernelOf, List.map_nil, guided, walk, List.mem_singleton] at member
      subst member
      exact agrees
  | [], _ :: _, fits, _, _, _, _, _ => by have := fits.modes; simp at this
  | _ :: _, [], fits, _, _, _, _, _ => by have := fits.modes; simp at this
  | (m, p) :: pats, (use, a) :: g, fits, σ, w, member, agrees, solved => by
      have rest : Fits pats g :=
        ⟨by have := fits.modes; simp only [List.map_cons, List.cons.injEq] at this; exact this.2,
          fun e inside => fits.ground e (List.mem_cons_of_mem _ inside)⟩
      have groundA : isGroundAtom a = true := fits.ground (use, a) (List.mem_cons_self ..)
      have shape : guided (kernelOf ((m, p) :: pats)) ((use, a) :: g) =
          Conj.pat use a :: Conj.as p a :: guided (kernelOf pats) g := rfl
      rw [shape] at member
      obtain ⟨r, picked, v, later, rfl⟩ := mem_walk_pat.mp member
      obtain ⟨rfl, _⟩ := (mem_matchesIn_ground groundA).mp picked
      simp only [walk] at later
      cases matched : matchAtom σ p a with
      | none => simp [matched] at later
      | some τ =>
          simp only [matched] at later
          cases solved with
          | cons head tail =>
              exact walk_guided_kernel_agrees pats g rest (w := v) later
                (rel_agrees (matchAtom_sound matched) agrees head) tail

/-- **A branch of a guarded kernel that fires is admitted by the first-order step**, with
its absences as checks: the absences are evaluated again when the branch fires, against the
store as it is then, and hold at every solution of the branch's equations. -/
theorem guarded_branch_fire_admitted {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats g : Footprint} {absents : List Atom} (fits : Fits pats g)
    {emit : Subst → Answers} {out : Answers}
    (fired : LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit =
      some (s', out)) :
    ∃ (sel : Selection O) (rows' : List O),
      Realizes label rows g sel ∧
      (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
          (guardedRule pats absents, sel)).Valid atomAction label ⟨[], rows.toFinset⟩ ∧
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' := by
  obtain ⟨c, member, sel, rows', real, _, same, rep', _, _⟩ := fire_publishes rep fired
  obtain ⟨w, walked, rfl⟩ := List.mem_map.mp member
  rw [guided_guarded pats g absents fits, List.append_nil, walk_append] at walked
  obtain ⟨k, kernelRow, inside⟩ := List.mem_flatMap.mp walked
  obtain ⟨v, absentRow, rfl⟩ := List.mem_map.mp inside
  obtain ⟨rfl, none⟩ := (mem_walk_absents absents).mp absentRow
  have footprint : (Candidate.footprint ⟨k.2 ++ [], [(k.1, [])]⟩) = k.2 := by
    simp [Candidate.footprint]
  rw [footprint] at real
  obtain ⟨isGuide, solved⟩ := walk_guided_kernel_solves pats g fits kernelRow
  have valid := guarded_valid_of rep ground
    (solved (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl k.1))
    (fun ρ each => walk_guided_kernel_agrees pats g fits kernelRow (agrees_nil ρ)
      (by rw [← isGuide]; exact each))
    none real
  rw [isGuide] at real
  exact ⟨sel, rows', real, (Firing.valid_ofPlain_iff atomAction label _ _).mpr valid, same, rep'⟩

/-- A proposal of a guarded kernel on a ground store fits its kernel. -/
theorem guarded_proposal_fits {s : Store} (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {absents : List Atom} {g : Footprint}
    (member : g ∈ proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩) : Fits pats g := by
  obtain ⟨σ, proposed⟩ := mem_proposals.mp member
  rw [walk_append] at proposed
  obtain ⟨k, kernelRow, inside⟩ := List.mem_flatMap.mp proposed
  obtain ⟨v, absentRow, same⟩ := List.mem_map.mp inside
  obtain ⟨rfl, _⟩ := (mem_walk_absents absents).mp absentRow
  have footprint : g = k.2 := by
    have := congrArg Prod.snd same
    simpa using this.symm
  rw [footprint]
  exact proposal_fits ground (σ := k.1) (g := k.2) kernelRow

/-- A firing leaves only atoms that were stored: a ground store stays ground. -/
theorem fire_keeps_ground {s s' : Store} {g : Footprint} {src : Sources}
    {emit : Subst → Answers} {out : Answers}
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (fired : LibTransform.fire s g src emit = some (s', out)) :
    ∀ a ∈ s', isGroundAtom a = true := by
  obtain ⟨_, c, _, _, _, _, rfl, _⟩ := fire_eq_some_iff.mp fired
  intro a member
  have positive : 0 < (commit c.footprint s).count a := List.count_pos_iff.mpr member
  rw [count_commit] at positive
  exact ground a (List.count_pos_iff.mp (by omega))

/-- **A transform of a kernel of reads and takes guarded by absences is a run of admitted
firings.** On a ground store represented by `rows`, the call is a run over its proposals in
which every branch that fires realizes its own proposal and is admitted by
`firstOrder atomAction label` for `guardedRule pats absents`: its absences are checks that
hold, at the store as it is when the branch fires, at every solution of the branch's
equations. Every other branch is refused because no candidate of it has a selection. -/
theorem guarded_transform_admitted_run {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (pats : Footprint) (absents : List Atom) (template : Atom) :
    ∃ rows' : List O,
      AdmittedRun label ⟨kernelOf pats ++ absentsOf absents, [], none⟩
        (guardedRule pats absents) rows s
        (proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩) rows'
        ((transform ⟨kernelOf pats ++ absentsOf absents, [], none⟩ template s).drain).2 ∧
      Represents label rows'
        ((transform ⟨kernelOf pats ++ absentsOf absents, [], none⟩ template s).drain).2 := by
  obtain ⟨rows', run, rep'⟩ :=
    fold_admitted (label := label) ⟨kernelOf pats ++ absentsOf absents, [], none⟩
      (guardedRule pats absents) (instances template) (Fits pats)
      (fun store => ∀ a ∈ store, isGroundAtom a = true)
      (fun holds fired => fire_keeps_ground holds fired)
      (fun rep holds fits fired => guarded_branch_fire_admitted rep holds fits fired)
      _ (fun g member => guarded_proposal_fits ground member) ([], s) rows rep ground
  rw [transform, transformWith_drain]
  exact ⟨rows', run, rep'⟩

namespace Controls

/-- With `b` stored, the kernel that takes `a` when `b` is absent has no row. -/
theorem absent_refuses_when_present :
    walk [a, b] true [] (kernelOf [(Mode.take, a)] ++ absentsOf [b]) = [] := by
  decide

/-- Without `b` stored it has its one row. -/
theorem absent_admits_when_absent :
    (walk [a] true [] (kernelOf [(Mode.take, a)] ++ absentsOf [b])).length = 1 := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
