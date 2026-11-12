import Mettapedia.Languages.MeTTa.PeTTa.LibTransformRenaming

/-!
# A transform call is one run of the first-order step

`LibTransformAbsent.guarded_transform_admitted_run` admits each fired branch of a call from
a configuration with no knowledge. The step keeps what its firings told, so one run of the
step starts each firing from the knowledge its predecessors left. This module builds that
run for a kernel of reads and takes guarded by absences, on a ground store.

* The rule instance of the firing with number `n` is the guarded rule with every variable
  tagged `n` (`RuleInstance.map (rename n)`), so no two firings of the run share a
  variable.
* `renamed_valid_of`: such a firing is valid at a configuration whose knowledge `K` is
  consistent and mentions only variables with smaller tags. Its equations are consistent
  with `K` because a solution of `K` extends over the firing's own variables
  (`withLocal`); its absences hold at every solution of all the equations because such a
  solution, untagged, is a solution of the firing's own equations (`untagged`).
* `guarded_transform_executable`: the fired branches of a `transform` call, in proposal
  order, with those rule instances, are an executable word of the step
  (`AnnotatedRuns.Executable`) from the configuration with the rows' occurrences and no
  knowledge. The word leaves a configuration whose occurrences are the rows representing
  the store the call leaves.
* `guarded_transform_is_run`: hence a run of `firstOrder atomAction label`
  (`AnnotatedRuns.executable_iff_run`), ending in consistent knowledge.

Scope: instances go to the caller, so no occurrence is made; `absent` of one pattern; a
ground store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction Check EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
  (Firing Executable follow firstOrder executable_iff_run follow_eq_last)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (publish publish_present)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## What a fired branch provides -/

/-- A branch of a guarded kernel that fires provides: bindings `σ` under which its patterns
are its guide's atoms; the fact that every solution of those equations agrees with `σ`;
the absences, with nothing matching under `σ`; a selection realizing the guide; and rows
representing the store it leaves. -/
theorem guarded_branch_fire_data {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) {pats g : Footprint} {absents : List Atom}
    (fits : Fits pats g) {emit : Subst → Answers} {out : Answers}
    (fired : LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit =
      some (s', out)) :
    ∃ (σ : Subst) (sel : Selection O) (rows' : List O),
      Realizes label rows g sel ∧
      List.Forall₂ (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution σ) (e.2, f.2)) pats g ∧
      (∀ ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst,
        List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats g → Agrees ρ σ) ∧
      (∀ p ∈ absents, matchesIn s σ p = []) ∧
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
  have solvedHere := solved
    (Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookupExtends_refl k.1)
  rw [isGuide] at real solvedHere
  exact ⟨k.1, sel, rows', real, solvedHere,
    fun ρ each => walk_guided_kernel_agrees pats g fits kernelRow (agrees_nil ρ) each,
    none, same, rep'⟩

/-! ## One firing, from knowledge -/

/-- From a relation with the image of a list back to the list, where the elements may be
used as members. -/
theorem forall₂_of_map_mem {α β γ : Type} {R : α → γ → Prop} {S : α → β → Prop} {f : β → γ} :
    ∀ {l : List α} {u : List β}, List.Forall₂ R l (u.map f) →
      (∀ a, ∀ b ∈ u, R a (f b) → S a b) → List.Forall₂ S l u
  | [], [], _, _ => List.Forall₂.nil
  | _ :: _, [], related, _ => by simp at related
  | [], _ :: _, related, _ => by simp at related
  | _ :: _, _ :: _, related, each => by
      simp only [List.map_cons, List.forall₂_cons] at related
      exact List.Forall₂.cons (each _ _ (List.mem_cons_self ..) related.1)
        (forall₂_of_map_mem related.2 fun a b member => each a b (List.mem_cons_of_mem _ member))

/-- A relation element by element, changed where the second elements may be used as
members. -/
theorem forall₂_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {u : List β}, List.Forall₂ R l u →
      (∀ a, ∀ b ∈ u, R a b → S a b) → List.Forall₂ S l u
  | _, _, .nil, _ => List.Forall₂.nil
  | _, _, .cons head tail, each =>
      List.Forall₂.cons (each _ _ (List.mem_cons_self ..) head)
        (forall₂_imp_mem tail fun a b member => each a b (List.mem_cons_of_mem _ member))

omit [DecidableEq O] in
/-- An equation between patterns and selected labels is a pattern and a selected label. -/
theorem mem_equations {label : O → Atom} :
    ∀ {patterns : List Atom} {selected : List O} {e : Atom × Atom},
      e ∈ Selection.equations label patterns selected →
        ∃ p ∈ patterns, ∃ o ∈ selected, e = (p, label o)
  | [], _, _, member => by simp [Selection.equations] at member
  | _ :: _, [], _, member => by simp [Selection.equations] at member
  | p :: patterns, o :: selected, e, member => by
      simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨p, List.mem_cons_self .., o, List.mem_cons_self .., rfl⟩
      · obtain ⟨p', inP, o', inO, same⟩ := mem_equations (label := label) member
        exact ⟨p', List.mem_cons_of_mem _ inP, o', List.mem_cons_of_mem _ inO, same⟩

/-- **A firing with fresh variables is valid from knowledge.** The guarded rule with every
variable tagged `n`, with a selection realizing a footprint that the kernel's patterns
solve, is valid at a configuration whose knowledge is consistent and mentions only
variables with tags below `n`. -/
theorem renamed_valid_of {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    {pats fp : Footprint} {absents : List Atom} {σ : Subst}
    (solved : List.Forall₂
      (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution σ) (e.2, f.2)) pats fp)
    (agreesOf : ∀ ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst,
      List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats fp → Agrees ρ σ)
    (none : ∀ p ∈ absents, matchesIn s σ p = []) {sel : Selection O}
    (real : Realizes label rows fp sel)
    {K : EquationStore Atom} {n : Nat} (consistent : atomAction.Consistent K)
    (below : ∀ e ∈ K, TagsBelow n e.1 ∧ TagsBelow n e.2) :
    sel.Valid atomAction label ((guardedRule pats absents).map (rename n))
      ⟨K, rows.toFinset⟩ := by
  have plain := selection_valid_of_solved solved real
  have modes := forall₂_modes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
  have groundLabel : ∀ o ∈ rows, isGroundAtom (label o) = true := fun o present =>
    ground _ (by rw [← rep.labels]; exact List.mem_map_of_mem present)
  have fixed : ∀ (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst), ∀ o ∈ rows,
      SubstitutionAlgebra.subst ρ (label o) = label o := fun ρ o present =>
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
      (vars_of_ground _ (groundLabel o present))
  have takeLength : ((takes pats).map (rename n)).length = sel.taken.length := by
    rw [List.length_map]; exact plain.take_length
  have readLength : ((reads pats).map (rename n)).length = sel.read.length := by
    rw [List.length_map]; exact plain.read_length
  have takeLocal : List.Forall₂ (fun p o => SubstitutionAlgebra.subst (solution σ) p = label o)
      (takes pats) sel.taken := by
    have each := forall₂_takes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
    rw [← real.taken_labels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution σ) a =
        SubstitutionAlgebra.subst (solution σ) (label o) := equal
    rw [same, fixed _ o (real.taken_present o member)]
  have readLocal : List.Forall₂ (fun p o => SubstitutionAlgebra.subst (solution σ) p = label o)
      (reads pats) sel.read := by
    have each := forall₂_reads (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
    rw [← real.read_labels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution σ) a =
        SubstitutionAlgebra.subst (solution σ) (label o) := equal
    rw [same, fixed _ o (real.read_present o member)]
  refine ⟨real.taken_distinct, by rw [real.made_none]; exact List.nodup_nil, takeLength,
    readLength, by simp [RuleInstance.map, guardedRule, real.made_none], real.enabled, ?_, ?_⟩
  · -- consistent: a solution of the knowledge, extended over the firing's own variables
    obtain ⟨ρ, models⟩ := consistent
    refine ⟨withLocal ρ n (solution σ), ?_⟩
    simp only [Selection.problem, RuleInstance.map, guardedRule, List.map_nil, List.append_nil,
      SubstitutionAction.models_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro e member
      have old : SubstitutionAlgebra.subst ρ e.1 = SubstitutionAlgebra.subst ρ e.2 :=
        models e member
      show SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) e.1 =
        SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) e.2
      rw [subst_withLocal_of_tagsBelow ρ (solution σ) (below e member).1,
        subst_withLocal_of_tagsBelow ρ (solution σ) (below e member).2]
      exact old
    · refine (Selection.models_equations_iff atomAction _ label takeLength).mpr ?_
      refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem takeLocal ?_)
      intro p o member here
      show SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) (rename n p) =
        SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) (label o)
      rw [subst_withLocal_rename ρ (solution σ) n p (label o) here
          (groundLabel o (real.taken_present o member)),
        fixed _ o (real.taken_present o member)]
    · refine (Selection.models_equations_iff atomAction _ label readLength).mpr ?_
      refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem readLocal ?_)
      intro p o member here
      show SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) (rename n p) =
        SubstitutionAlgebra.subst (withLocal ρ n (solution σ)) (label o)
      rw [subst_withLocal_rename ρ (solution σ) n p (label o) here
          (groundLabel o (real.read_present o member)),
        fixed _ o (real.read_present o member)]
  · -- checks: a solution of everything is, untagged, a solution of the firing's equations
    intro check member ρ models
    change check ∈ (absents.map Check.absent).map (Check.map (rename n)) at member
    obtain ⟨plainCheck, inChecks, rfl⟩ := List.mem_map.mp member
    obtain ⟨p, inside, rfl⟩ := List.mem_map.mp inChecks
    have parts : atomAction.Models ρ
        (Selection.equations label ((takes pats).map (rename n)) sel.taken) ∧
        atomAction.Models ρ
          (Selection.equations label ((reads pats).map (rename n)) sel.read) := by
      have all : atomAction.Models ρ
          (sel.problem label ((guardedRule pats absents).map (rename n))
            ⟨K, rows.toFinset⟩) := models
      simp only [Selection.problem, RuleInstance.map, guardedRule, List.map_nil,
        List.append_nil, SubstitutionAction.models_append] at all
      exact ⟨all.1.2, all.2⟩
    have takeSolved : List.Forall₂
        (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (takes pats) (takes fp) := by
      rw [← real.taken_labels]
      have each := List.forall₂_map_left_iff.mp
        ((Selection.models_equations_iff atomAction ρ label takeLength).mp parts.1)
      refine forall₂_map_of_mem each ?_
      intro a o member equal
      have same : SubstitutionAlgebra.subst ρ (rename n a) =
          SubstitutionAlgebra.subst ρ (label o) := equal
      rw [fixed ρ o (real.taken_present o member)] at same
      exact subst_untagged_of_rename ρ n a (label o) same
        (groundLabel o (real.taken_present o member))
    have readSolved : List.Forall₂
        (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (reads pats) (reads fp) := by
      rw [← real.read_labels]
      have each := List.forall₂_map_left_iff.mp
        ((Selection.models_equations_iff atomAction ρ label readLength).mp parts.2)
      refine forall₂_map_of_mem each ?_
      intro a o member equal
      have same : SubstitutionAlgebra.subst ρ (rename n a) =
          SubstitutionAlgebra.subst ρ (label o) := equal
      rw [fixed ρ o (real.read_present o member)] at same
      exact subst_untagged_of_rename ρ n a (label o) same
        (groundLabel o (real.read_present o member))
    have agrees : Agrees (untagged ρ n) σ :=
      agreesOf _ (forall₂_of_takes_reads modes takeSolved readSolved)
    have own := absent_check_holds rep ground (none p inside) agrees
    show ∀ o ∈ rows.toFinset,
      ¬ atomAction.E (atomAction.apply ρ (rename n p)) (atomAction.apply ρ (label o))
    intro o present equal
    have inRows : o ∈ rows := List.mem_toFinset.mp present
    have same : SubstitutionAlgebra.subst ρ (rename n p) =
        SubstitutionAlgebra.subst ρ (label o) := equal
    rw [fixed ρ o inRows] at same
    have untaggedSame := subst_untagged_of_rename ρ n p (label o) same (groundLabel o inRows)
    refine own o present ?_
    show SubstitutionAlgebra.subst (untagged ρ n) p =
      SubstitutionAlgebra.subst (untagged ρ n) (label o)
    rw [untaggedSame, fixed _ o inRows]

/-! ## The whole call -/

/-- The fold of the branches of a guarded kernel is an executable word of the step: each
fired branch contributes the guarded rule with fresh variables, valid at the configuration
its predecessors left. -/
theorem guarded_fold_executable {label : O → Atom} (pats : Footprint) (absents : List Atom)
    (emit : Subst → Answers) :
    ∀ (guides : List Footprint), (∀ g ∈ guides, Fits pats g) →
      ∀ (acc : List Atom × Store) (rows : List O) (K : EquationStore Atom) (n : Nat),
        Represents label rows acc.2 → (∀ a ∈ acc.2, isGroundAtom a = true) →
        atomAction.Consistent K → (∀ e ∈ K, TagsBelow n e.1 ∧ TagsBelow n e.2) →
        ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
          (rows' : List O),
          Executable atomAction label ⟨K, rows.toFinset⟩ word ∧
          (follow label ⟨K, rows.toFinset⟩ word).present = rows'.toFinset ∧
          Represents label rows'
            (guides.foldl
              (branchStep toCaller ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit) acc).2 ∧
          (∀ f ∈ word, ∃ m, f.rule = (guardedRule pats absents).map (rename m) ∧
            f.queries = []) ∧
          word.length ≤ guides.length
  | [], _, acc, rows, K, n, rep, _, consistent, _ =>
      ⟨[], rows, consistent, rfl, rep, by simp, Nat.le_refl _⟩
  | g :: guides, fits, acc, rows, K, n, rep, ground, consistent, below => by
      have later : ∀ g' ∈ guides, Fits pats g' := fun g' member =>
        fits g' (List.mem_cons_of_mem _ member)
      cases fired : LibTransform.fire acc.2 g
          ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit with
      | none =>
          have same : branchStep toCaller ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit
              acc g = acc := by
            simp [branchStep, fired]
          obtain ⟨word, rows', exec, present, rep', rules, len⟩ :=
            guarded_fold_executable pats absents emit guides later acc rows K n rep ground
              consistent below
          refine ⟨word, rows', exec, present, ?_, rules, Nat.le_succ_of_le len⟩
          rw [List.foldl_cons, same]
          exact rep'
      | some result =>
          obtain ⟨s', out⟩ := result
          have next : branchStep toCaller ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit
              acc g = (acc.1 ++ out, s') := by
            simp [branchStep, fired]
          obtain ⟨σ, sel, mid, real, solved, agreesOf, none, published, represented⟩ :=
            guarded_branch_fire_data rep (fits g (List.mem_cons_self ..)) fired
          have valid := renamed_valid_of rep ground solved agreesOf none real consistent below
          have groundLabel : ∀ o ∈ rows, isGroundAtom (label o) = true := fun o present =>
            ground _ (by rw [← rep.labels]; exact List.mem_map_of_mem present)
          have present : mid.toFinset =
              Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire
                rows.toFinset (sel.commit (T := Atom)) := by
            rw [List.toFinset_eq_of_perm _ _ published, publish_present]
            rfl
          have belowNext : ∀ e ∈ sel.problem label
              ((guardedRule pats absents).map (rename n)) ⟨K, rows.toFinset⟩,
              TagsBelow (n + 1) e.1 ∧ TagsBelow (n + 1) e.2 := by
            intro e member
            simp only [Selection.problem, RuleInstance.map, guardedRule, List.map_nil,
              List.append_nil, List.mem_append] at member
            rcases member with (old | taken) | read
            · exact ⟨(below e old).1.mono (Nat.le_succ n), (below e old).2.mono (Nat.le_succ n)⟩
            · obtain ⟨p', inP, o, inO, rfl⟩ := mem_equations taken
              obtain ⟨p, _, rfl⟩ := List.mem_map.mp inP
              exact ⟨tagsBelow_rename n p,
                tagsBelow_of_ground _ (groundLabel o (real.taken_present o inO))⟩
            · obtain ⟨p', inP, o, inO, rfl⟩ := mem_equations read
              obtain ⟨p, _, rfl⟩ := List.mem_map.mp inP
              exact ⟨tagsBelow_rename n p,
                tagsBelow_of_ground _ (groundLabel o (real.read_present o inO))⟩
          obtain ⟨word, rows', exec, present', rep', rules, len⟩ :=
            guarded_fold_executable pats absents emit guides later (acc.1 ++ out, s') mid
              (sel.problem label ((guardedRule pats absents).map (rename n))
                ⟨K, rows.toFinset⟩) (n + 1) represented (fire_keeps_ground ground fired)
              valid.consistent belowNext
          have result :
              (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
                ((guardedRule pats absents).map (rename n), sel)).result label
                  ⟨K, rows.toFinset⟩ =
                ⟨sel.problem label ((guardedRule pats absents).map (rename n))
                  ⟨K, rows.toFinset⟩, mid.toFinset⟩ := by
            rw [present]
            rfl
          refine ⟨Firing.ofPlain ((guardedRule pats absents).map (rename n), sel) :: word,
            rows', ?_, ?_, ?_, ?_, Nat.succ_le_succ len⟩
          · refine ⟨(Firing.valid_ofPlain_iff atomAction label _ _).mpr valid, ?_⟩
            rw [result]
            exact exec
          · show (follow label
              ((Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
                ((guardedRule pats absents).map (rename n), sel)).result label
                  ⟨K, rows.toFinset⟩) word).present = rows'.toFinset
            rw [result]
            exact present'
          · rw [List.foldl_cons, next]
            exact rep'
          · intro f member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨n, rfl, rfl⟩
            · exact rules f member

/-- **A transform call is an executable word of the first-order step.** On a ground store
represented by `rows`, the fired branches of a call of a kernel of reads and takes guarded
by absences, in proposal order, each with the guarded rule written in fresh variables, are
executable from the configuration with the rows' occurrences and no knowledge: each firing
is valid at the configuration its predecessors left, knowledge included. The word leaves a
configuration whose occurrences are the rows that represent the store the call leaves. -/
theorem guarded_transform_executable {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (pats : Footprint) (absents : List Atom) (template : Atom) :
    ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
      (rows' : List O),
      Executable atomAction label ⟨[], rows.toFinset⟩ word ∧
      (follow label ⟨[], rows.toFinset⟩ word).present = rows'.toFinset ∧
      Represents label rows'
        ((transform ⟨kernelOf pats ++ absentsOf absents, [], none⟩ template s).drain).2 ∧
      (∀ f ∈ word, ∃ m, f.rule = (guardedRule pats absents).map (rename m) ∧
        f.queries = []) ∧
      word.length ≤ (proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩).length := by
  obtain ⟨word, rows', exec, present, rep', rules, len⟩ :=
    guarded_fold_executable (label := label) pats absents (instances template) _
      (fun g member => guarded_proposal_fits ground member) ([], s) rows [] 0 rep ground
      ⟨Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty, by intro e member; simp at member⟩
      (by intro e member; simp at member)
  rw [transform, transformWith_drain]
  exact ⟨word, rows', exec, present, rep', rules, len⟩

/-- **A transform call is a run of the first-order step.** The fired branches of the call
are a run of `firstOrder atomAction label` from the configuration with the rows'
occurrences and no knowledge; the run ends in consistent knowledge, at a configuration
whose occurrences are the rows that represent the store the call leaves. -/
theorem guarded_transform_is_run {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (pats : Footprint) (absents : List Atom) (template : Atom) :
    ∃ (run : (firstOrder atomAction label).Run (⟨[], rows.toFinset⟩ : Configuration Atom O))
      (rows' : List O),
      run.last.present = rows'.toFinset ∧
      atomAction.Consistent run.last.equations ∧
      Represents label rows'
        ((transform ⟨kernelOf pats ++ absentsOf absents, [], none⟩ template s).drain).2 := by
  obtain ⟨word, rows', exec, present, rep', _, _⟩ :=
    guarded_transform_executable rep ground pats absents template
  obtain ⟨run, isWord, consistent⟩ :=
    (executable_iff_run atomAction label _ word).mp exec
  refine ⟨run, rows', ?_, consistent, rep'⟩
  rw [← follow_eq_last atomAction label run, isWord]
  exact present

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
