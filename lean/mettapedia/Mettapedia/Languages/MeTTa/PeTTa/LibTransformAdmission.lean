import Mettapedia.Languages.MeTTa.PeTTa.LibTransformRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# A kernel firing of the library's model is admitted by the first-order step

`LibTransformStep` shows that a firing of the model is an enabled occurrence commit. The
first-order step (`AnnotatedRuns.firstOrder`) asks more of a firing: a rule instance whose
patterns, set equal to the labels of the selected occurrences, have a common solution
(`Selection.Valid`). This module supplies that for a kernel of reads and takes on a ground
store.

* `solution`: the bindings of a walk, as a substitution of the step's atom action;
  `applySubst_eq_subst` says the two ways of applying them agree.
* `match_solves`: a match of a pattern against a ground atom solves the equation between
  them, under its bindings and under every extension of them.
* `walk_kernel_solves`: a row of a kernel of reads and takes solves, conjunct by conjunct,
  the equation between each pattern and the atom the row picked for it.
* `kernel_selection_valid`: with a selection realizing the row's footprint, the rule
  instance whose takes and reads are the kernel's patterns as written (`kernelRule`) is
  valid at the configuration with those occurrences and no knowledge.
* `kernel_fire_admitted`: a firing of such a kernel is an admitted firing of
  `firstOrder atomAction label`, and the store it leaves is represented by a permutation of
  the ordered publication.
* `Fits`, `proposal_fits`, `walk_guided_kernel_solves`, `branch_fire_admitted`: the same
  for a branch, the kernel guided by one of its proposals. The branch reads or takes the
  atom its proposal matched and `(tf:as P A)` tells that the pattern is that atom; its
  footprint is the guide itself, and its firing is admitted for the same rule instance.

* `AdmittedRun`, `kernel_transform_admitted_run`: a whole `transform` call of such a kernel
  on a ground store is a run over its proposals in which every branch that fires realizes
  its own proposal and is admitted by the step, and every other branch is refused.

Scope. The configuration has no knowledge: this is one firing whose variables are its own.
A later firing of a run starts from the knowledge the earlier ones left, so its rule must be
written with variables fresh for that knowledge; the model starts each firing from no
bindings, which is that freshness. The conjuncts `absent`, `unique`, `collect` and the
`all` extension are not covered here.

Negative example: `Controls.unmatched_pattern_has_no_row` (a kernel whose pattern matches
nothing has no row, so nothing fires and no selection is asked for).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst matchAtom applySubst isGroundAtom matchAtom_applySubst_ground applySubst_ground_ext)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns (Firing)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (publish)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst SubstitutionAlgebra.vars)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## Bindings as a solution -/

/-- The substitution a list of bindings denotes. -/
def solution (σ : Subst) : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst :=
  fun v => Subst.lookup σ v

/-- Applying a list of bindings is substituting its solution. -/
theorem applySubst_eq_subst (σ : Subst) :
    ∀ a : Atom, applySubst σ a = SubstitutionAlgebra.subst (solution σ) a
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es => by
      simp only [applySubst, SubstitutionAlgebra.subst]
      congr 1
      exact list es
where
  list : ∀ es : List Atom,
      applySubst.applySubstList σ es = SubstitutionAlgebra.subst.substList (solution σ) es
    | [] => rfl
    | a :: as => by
        simp only [applySubst.applySubstList, SubstitutionAlgebra.subst.substList,
          applySubst_eq_subst σ a, list as]

/-- A ground atom has no variable. -/
theorem vars_of_ground : ∀ a : Atom, isGroundAtom a = true → SubstitutionAlgebra.vars a = []
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => rfl
  | .grounded _, _ => rfl
  | .expression es, ground => by
      simp only [isGroundAtom] at ground
      simp only [SubstitutionAlgebra.vars]
      exact list es ground
where
  list : ∀ es : List Atom, isGroundAtom.isGroundList es = true →
      SubstitutionAlgebra.vars.varsList es = []
    | [], _ => rfl
    | a :: as, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [SubstitutionAlgebra.vars.varsList, vars_of_ground a ground.1,
          list as ground.2, List.append_nil]

/-- **A match solves its equation.** A pattern matched against a ground atom is equal to
it under the bindings of the match, and under every extension of them. -/
theorem match_solves {σ τ ρ : Subst} {p b : Atom} (matched : matchAtom σ p b = some τ)
    (ground : isGroundAtom b = true) (ext : Subst.lookupExtends ρ τ) :
    atomAction.Solves (solution ρ) (p, b) := by
  have here : applySubst τ p = b := matchAtom_applySubst_ground σ p b τ matched ground
  have later : applySubst ρ p = b := by
    rw [applySubst_ground_ext ext (by rw [here]; exact ground), here]
  show SubstitutionAlgebra.subst (solution ρ) p = SubstitutionAlgebra.subst (solution ρ) b
  rw [← applySubst_eq_subst, later,
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
      (vars_of_ground b ground)]

/-! ## A kernel of reads and takes -/

/-- The kernel that reads or takes each pattern, in order. -/
def kernelOf (pats : Footprint) : List Conj := pats.map fun e => .pat e.1 e.2

/-- The rule instance of such a kernel: its patterns as written. It tells nothing, checks
nothing and makes nothing. -/
def kernelRule (pats : Footprint) : RuleInstance Atom := ⟨takes pats, reads pats, [], [], []⟩

/-- A row of the kernel solves, conjunct by conjunct, the equation between the pattern and
the atom picked for it, under every extension of the row's bindings; the modes agree. -/
theorem walk_kernel_solves {s : Store} {firing : Bool}
    (ground : ∀ a ∈ s, isGroundAtom a = true) :
    ∀ (pats : Footprint) {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (kernelOf pats) →
      ∀ {ρ : Subst}, Subst.lookupExtends ρ w.1 →
        List.Forall₂ (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution ρ) (e.2, f.2)) pats w.2
  | [], σ, w, member, ρ, _ => by
      simp only [kernelOf, List.map_nil, walk, List.mem_singleton] at member
      subst member
      exact List.Forall₂.nil
  | (m, p) :: pats, σ, w, member, ρ, ext => by
      obtain ⟨r, picked, v, later, rfl⟩ :=
        (mem_walk_pat (m := m) (p := p) (cs := kernelOf pats)).mp member
      obtain ⟨stored, matched⟩ := mem_matchesIn.mp picked
      have extends' := (walk_sound later).1
      exact List.Forall₂.cons
        ⟨rfl, match_solves matched (ground _ stored)
          (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_trans extends' ext)⟩
        (walk_kernel_solves ground pats later ext)

/-- Conjunct by conjunct relates the takes among themselves. -/
theorem forall₂_takes {R : Atom → Atom → Prop} :
    ∀ {pats fp : Footprint},
      List.Forall₂ (fun e f => e.1 = f.1 ∧ R e.2 f.2) pats fp →
        List.Forall₂ R (takes pats) (takes fp)
  | _, _, .nil => List.Forall₂.nil
  | (m, p) :: _, (_, b) :: _, .cons ⟨same, related⟩ rest => by
      cases same
      cases m
      · simpa [takes] using forall₂_takes rest
      · simpa [takes] using List.Forall₂.cons related (forall₂_takes rest)

/-- Conjunct by conjunct relates the reads among themselves. -/
theorem forall₂_reads {R : Atom → Atom → Prop} :
    ∀ {pats fp : Footprint},
      List.Forall₂ (fun e f => e.1 = f.1 ∧ R e.2 f.2) pats fp →
        List.Forall₂ R (reads pats) (reads fp)
  | _, _, .nil => List.Forall₂.nil
  | (m, p) :: _, (_, b) :: _, .cons ⟨same, related⟩ rest => by
      cases same
      cases m
      · simpa [reads] using List.Forall₂.cons related (forall₂_reads rest)
      · simpa [reads] using forall₂_reads rest

/-- **A footprint that solves the kernel's patterns, realized, is a valid selection of the
step.** At the configuration with the rows' occurrences and no knowledge, the rule instance
whose takes and reads are the kernel's patterns is valid with the selection: its patterns
and the selected labels have `σ` as a common solution. -/
theorem selection_valid_of_solved {label : O → Atom} {rows : List O} {pats fp : Footprint}
    {σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst}
    (solved : List.Forall₂ (fun e f => e.1 = f.1 ∧ atomAction.Solves σ (e.2, f.2)) pats fp)
    {sel : Selection O} (real : Realizes label rows fp sel) :
    sel.Valid atomAction label (kernelRule pats) ⟨[], rows.toFinset⟩ := by
  have takeSolved := forall₂_takes (R := fun p b => atomAction.Solves σ (p, b)) solved
  have readSolved := forall₂_reads (R := fun p b => atomAction.Solves σ (p, b)) solved
  have takeLength : (takes pats).length = sel.taken.length := by
    rw [takeSolved.length_eq, ← real.taken_labels, List.length_map]
  have readLength : (reads pats).length = sel.read.length := by
    rw [readSolved.length_eq, ← real.read_labels, List.length_map]
  refine ⟨real.taken_distinct, by rw [real.made_none]; exact List.nodup_nil, takeLength,
    readLength, by rw [real.made_none]; rfl, real.enabled, ⟨σ, ?_⟩, ?_⟩
  · simp only [Selection.problem, kernelRule, List.nil_append, List.append_nil,
      SubstitutionAction.models_append]
    refine ⟨(Selection.models_equations_iff atomAction _ label takeLength).mpr ?_,
      (Selection.models_equations_iff atomAction _ label readLength).mpr ?_⟩
    · rw [← real.taken_labels] at takeSolved
      exact (List.forall₂_map_right_iff (f := label)
        (R := fun p b => atomAction.Solves σ (p, b))).mp takeSolved
    · rw [← real.read_labels] at readSolved
      exact (List.forall₂_map_right_iff (f := label)
        (R := fun p b => atomAction.Solves σ (p, b))).mp readSolved
  · intro check member
    simp [kernelRule] at member

/-- **A realized row of the kernel is a valid selection of the step.** -/
theorem kernel_selection_valid {label : O → Atom} {rows : List O} {s : Store}
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {firing : Bool} {w : Subst × Footprint}
    (walked : w ∈ walk s firing [] (kernelOf pats)) {sel : Selection O}
    (real : Realizes label rows w.2 sel) :
    sel.Valid atomAction label (kernelRule pats) ⟨[], rows.toFinset⟩ :=
  selection_valid_of_solved (walk_kernel_solves ground pats walked
    (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl w.1)) real

/-- Without a guide the kernel is fired as written. -/
theorem guided_kernelOf_nil : ∀ pats : Footprint, guided (kernelOf pats) [] = kernelOf pats
  | [] => rfl
  | (m, p) :: pats => by
      show Conj.pat m p :: guided (kernelOf pats) [] = Conj.pat m p :: kernelOf pats
      rw [guided_kernelOf_nil pats]

/-- **A firing of a kernel of reads and takes is an admitted firing of the first-order
step.** On a ground store represented by `rows`, when the model fires the kernel `pats` it
does so with a selection that the step admits for the rule instance `kernelRule pats` at
the configuration with those occurrences and no knowledge; the store it leaves is
represented by a permutation of the ordered publication. -/
theorem kernel_fire_admitted {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {emit : Subst → Answers} {out : Answers}
    (fired : LibTransform.fire s [] ⟨kernelOf pats, [], none⟩ emit = some (s', out)) :
    ∃ (sel : Selection O) (rows' : List O),
      (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
          (kernelRule pats, sel)).Valid atomAction label ⟨[], rows.toFinset⟩ ∧
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' := by
  obtain ⟨c, member, sel, rows', real, _, same, rep', _, _⟩ := fire_publishes rep fired
  obtain ⟨k, walked, rfl⟩ := List.mem_map.mp member
  rw [guided_kernelOf_nil, List.append_nil] at walked
  have footprint : (Candidate.footprint ⟨k.2, [(k.1, [])]⟩) = k.2 := by
    simp [Candidate.footprint]
  rw [footprint] at real
  exact ⟨sel, rows', (Firing.valid_ofPlain_iff atomAction label _ _).mpr
    (kernel_selection_valid ground walked real), same, rep'⟩

/-! ## A branch: the kernel guided by its proposal -/

/-- A guide fits a kernel when it has one entry for each conjunct, in the conjunct's mode,
and its atoms are ground. A proposal of the kernel on a ground store is such a guide
(`proposal_fits`). -/
structure Fits (pats g : Footprint) : Prop where
  modes : pats.map Prod.fst = g.map Prod.fst
  ground : ∀ e ∈ g, isGroundAtom e.2 = true

/-- Conjunct by conjunct, the modes agree. -/
theorem forall₂_modes {R : Atom → Atom → Prop} :
    ∀ {pats fp : Footprint},
      List.Forall₂ (fun e f => e.1 = f.1 ∧ R e.2 f.2) pats fp →
        pats.map Prod.fst = fp.map Prod.fst
  | _, _, .nil => rfl
  | _ :: _, _ :: _, .cons head rest => by
      simp only [List.map_cons, head.1, forall₂_modes rest]

/-- A proposal of the kernel on a ground store fits it. -/
theorem proposal_fits {s : Store} (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats : Footprint} {σ : Subst} {g : Footprint}
    (proposed : (σ, g) ∈ walk s false [] (kernelOf pats)) : Fits pats g := by
  have solved := walk_kernel_solves ground pats proposed
    (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl σ)
  exact ⟨forall₂_modes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved,
    fun e member => ground _ ((walk_sound proposed).2 e member)⟩

/-- A row of the kernel guided by `g` has exactly the footprint `g`, and its bindings solve,
conjunct by conjunct, the equation between each pattern and the guide's atom: the branch
reads or takes the atom its proposal matched, and `(tf:as P A)` tells that the pattern is
that atom. -/
theorem walk_guided_kernel_solves {s : Store} {firing : Bool} :
    ∀ (pats g : Footprint), Fits pats g → ∀ {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (guided (kernelOf pats) g) →
      w.2 = g ∧ ∀ {ρ : Subst}, Subst.lookupExtends ρ w.1 →
        List.Forall₂ (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution ρ) (e.2, f.2)) pats w.2
  | [], [], _, σ, w, member => by
      simp only [kernelOf, List.map_nil, guided, walk, List.mem_singleton] at member
      subst member
      exact ⟨rfl, fun _ => List.Forall₂.nil⟩
  | [], _ :: _, fits, _, _, _ => by have := fits.modes; simp at this
  | _ :: _, [], fits, _, _, _ => by have := fits.modes; simp at this
  | (m, p) :: pats, (use, a) :: g, fits, σ, w, member => by
      have sameMode : m = use := by
        have := fits.modes
        simp only [List.map_cons, List.cons.injEq] at this
        exact this.1
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
          obtain ⟨same, solved⟩ := walk_guided_kernel_solves pats g rest later
          have extends' := (walk_sound later).1
          refine ⟨by simp [same], fun {ρ} ext => ?_⟩
          exact List.Forall₂.cons
            ⟨sameMode, match_solves matched groundA
              (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_trans extends' ext)⟩
            (solved ext)

/-- **A branch that fires is an admitted firing of the first-order step.** For a kernel of
reads and takes and a guide that fits it (any of its proposals on a ground store), when the
model fires the branch at a store represented by `rows` it does so with a selection that
`firstOrder atomAction label` admits for the rule instance `kernelRule pats`, at the
configuration with those occurrences and no knowledge; the footprint is the guide itself,
and the store left is represented by a permutation of the ordered publication. -/
theorem branch_fire_admitted {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) {pats g : Footprint} (fits : Fits pats g)
    {emit : Subst → Answers} {out : Answers}
    (fired : LibTransform.fire s g ⟨kernelOf pats, [], none⟩ emit = some (s', out)) :
    ∃ (sel : Selection O) (rows' : List O),
      Realizes label rows g sel ∧
      (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
          (kernelRule pats, sel)).Valid atomAction label ⟨[], rows.toFinset⟩ ∧
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' := by
  obtain ⟨c, member, sel, rows', real, _, same, rep', _, _⟩ := fire_publishes rep fired
  obtain ⟨k, walked, rfl⟩ := List.mem_map.mp member
  rw [List.append_nil] at walked
  have footprint : (Candidate.footprint ⟨k.2, [(k.1, [])]⟩) = k.2 := by
    simp [Candidate.footprint]
  rw [footprint] at real
  obtain ⟨isGuide, solved⟩ := walk_guided_kernel_solves pats g fits walked
  have valid := selection_valid_of_solved
    (solved (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl k.1)) real
  rw [isGuide] at real
  exact ⟨sel, rows', real, (Firing.valid_ofPlain_iff atomAction label _ _).mpr valid, same, rep'⟩

/-! ## A whole call -/

/-- A run of branches of the sources `src`, each fired branch admitted by the first-order
step for the rule instance `rule`. `AdmittedRun label src rule rows s guides rows' s'`: from
the rows `rows` representing `s`, the branches of `guides`, in order, are refused or fire,
and leave the rows `rows'` representing `s'`. A branch that fires does so with a selection
that realizes its own guide and that `firstOrder atomAction label` admits for `rule` at the
configuration with the rows' occurrences and no knowledge. -/
inductive AdmittedRun (label : O → Atom) (src : Sources) (rule : RuleInstance Atom) :
    List O → Store → List Footprint → List O → Store → Prop
  | done (rows : List O) (s : Store) : AdmittedRun label src rule rows s [] rows s
  | refused {rows rows' : List O} {s s' : Store} {g : Footprint} {guides : List Footprint}
      (none : ∀ c ∈ candidates s g src,
        ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel)
      (rest : AdmittedRun label src rule rows s guides rows' s') :
      AdmittedRun label src rule rows s (g :: guides) rows' s'
  | fired {rows mid rows' : List O} {s middle s' : Store} {g : Footprint}
      {guides : List Footprint} {sel : Selection O}
      (real : Realizes label rows g sel)
      (admitted : (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
        (rule, sel)).Valid atomAction label ⟨[], rows.toFinset⟩)
      (published : mid.Perm (publish rows sel))
      (represented : Represents label mid middle)
      (rest : AdmittedRun label src rule mid middle guides rows' s') :
      AdmittedRun label src rule rows s (g :: guides) rows' s'

/-- The fold of the branches of `src` over guides of a kind whose fired branches are
admitted is an admitted run. `good` is the kind of guide (for a kernel, `Fits`), and
`admit` says that a branch of that kind which fires is admitted. `inv` is a property of the
store that firings keep (for example, that it is ground) and that `admit` may use. -/
theorem fold_admitted {label : O → Atom} (src : Sources) (rule : RuleInstance Atom)
    (emit : Subst → Answers) (good : Footprint → Prop) (inv : Store → Prop)
    (keep : ∀ {s s' : Store} {g : Footprint} {out : Answers},
      inv s → LibTransform.fire s g src emit = some (s', out) → inv s')
    (admit : ∀ {rows : List O} {s s' : Store} {g : Footprint} {out : Answers},
      Represents label rows s → inv s → good g →
      LibTransform.fire s g src emit = some (s', out) →
      ∃ (sel : Selection O) (rows' : List O), Realizes label rows g sel ∧
        (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
          (rule, sel)).Valid atomAction label ⟨[], rows.toFinset⟩ ∧
        rows'.Perm (publish rows sel) ∧ Represents label rows' s') :
    ∀ (guides : List Footprint), (∀ g ∈ guides, good g) →
      ∀ (acc : List Atom × Store) (rows : List O), Represents label rows acc.2 → inv acc.2 →
      ∃ rows' : List O,
        AdmittedRun label src rule rows acc.2 guides rows'
          (guides.foldl (branchStep toCaller src emit) acc).2 ∧
        Represents label rows' (guides.foldl (branchStep toCaller src emit) acc).2
  | [], _, acc, rows, rep, _ => ⟨rows, AdmittedRun.done rows acc.2, rep⟩
  | g :: guides, goods, acc, rows, rep, holds => by
      have later : ∀ g' ∈ guides, good g' := fun g' member =>
        goods g' (List.mem_cons_of_mem _ member)
      cases fired : LibTransform.fire acc.2 g src emit with
      | none =>
          have same : branchStep toCaller src emit acc g = acc := by
            simp [branchStep, fired]
          obtain ⟨rows', run, rep'⟩ :=
            fold_admitted src rule emit good inv keep admit guides later acc rows rep holds
          refine ⟨rows', ?_, ?_⟩
          · rw [List.foldl_cons, same]
            exact AdmittedRun.refused ((fire_eq_none_iff_unrealized rep).mp fired) run
          · rw [List.foldl_cons, same]
            exact rep'
      | some result =>
          obtain ⟨s', out⟩ := result
          have next : branchStep toCaller src emit acc g = (acc.1 ++ out, s') := by
            simp [branchStep, fired]
          obtain ⟨sel, mid, real, admitted, published, represented⟩ :=
            admit rep holds (goods g (List.mem_cons_self ..)) fired
          obtain ⟨rows', run, rep'⟩ :=
            fold_admitted src rule emit good inv keep admit guides later (acc.1 ++ out, s') mid
              represented (keep holds fired)
          refine ⟨rows', ?_, ?_⟩
          · rw [List.foldl_cons, next]
            exact AdmittedRun.fired real admitted published represented run
          · rw [List.foldl_cons, next]
            exact rep'

/-- **A transform of a kernel of reads and takes is a run of admitted firings.** On a
ground store represented by `rows`, the call is a run over its proposals in which every
branch that fires realizes exactly its own proposal and is admitted by
`firstOrder atomAction label` for the rule instance `kernelRule pats`; every other branch
is refused because no candidate of it has a selection. The store the call leaves is the
run's last store. -/
theorem kernel_transform_admitted_run {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (pats : Footprint) (template : Atom) :
    ∃ rows' : List O,
      AdmittedRun label ⟨kernelOf pats, [], none⟩ (kernelRule pats) rows s
        (proposals s ⟨kernelOf pats, [], none⟩) rows'
        ((transform ⟨kernelOf pats, [], none⟩ template s).drain).2 ∧
      Represents label rows' ((transform ⟨kernelOf pats, [], none⟩ template s).drain).2 := by
  have fits : ∀ g ∈ proposals s ⟨kernelOf pats, [], none⟩, Fits pats g := by
    intro g member
    obtain ⟨σ, proposed⟩ := mem_proposals.mp member
    exact proposal_fits ground proposed
  obtain ⟨rows', run, rep'⟩ :=
    fold_admitted (label := label) ⟨kernelOf pats, [], none⟩ (kernelRule pats)
      (instances template) (Fits pats) (fun _ => True) (fun _ _ => trivial)
      (fun rep _ fits fired => branch_fire_admitted rep fits fired) _ fits ([], s) rows rep
      trivial
  rw [transform, transformWith_drain]
  exact ⟨rows', run, rep'⟩

namespace Controls

/-- A kernel whose pattern matches no stored atom has no row: nothing fires, and no
selection is asked for. -/
theorem unmatched_pattern_has_no_row :
    walk [a, b] true [] (kernelOf [(Mode.take, .symbol "c")]) = [] := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
