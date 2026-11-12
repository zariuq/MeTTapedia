import Mettapedia.Languages.MeTTa.PeTTa.LibTransformResolved

/-!
# A transform that makes atoms is a run of the first-order step

`(transform SPACE SOURCES TEMPLATE SPACE)` adds its instances to the store. In the step a
firing that makes atoms makes occurrences whose labels are the rule's produce terms as
written, here the template's parts with the firing's own variables; the atoms the store
holds are those labels under the knowledge the run has told. This module proves that such
a call is a run of `firstOrder atomAction label`, for a kernel of reads and takes guarded
by absences, a template whose variables the kernel binds, and a ground store.

* `Knows label K n rows s`: the rows are distinct; the knowledge `K` is consistent; under
  every solution of `K` the rows' labels are the atoms of the store `s`, in order; the
  store is ground; `K` and the rows' labels mention only variables with tags below `n`.
  With no knowledge and ground labels this is `Represents` (`knows_of_represents`).
* `madeRule`: the rule instance whose takes and reads are the kernel's patterns, whose
  checks are the absences and whose produce is the template's parts.
* `made_fire_step`: a branch that fires is a valid firing of the made rule with variables
  tagged `n`, at the configuration with knowledge `K`; it makes fresh occurrences labelled
  with the renamed template parts; and the knowledge and rows it leaves know the store the
  model leaves (the committed store followed by the instances).
* `made_transform_is_run`: the whole call is a run of the step. At its end, under every
  solution of the knowledge, the labels of the last rows are the atoms of the store the
  call leaves, in order.

The supply of occurrences is a hypothesis: for every finite set and every label there is
an occurrence outside the set with that label.

Scope: one space, ground store, `absent` of one pattern, no `all` or `once`, a template
closed in the kernel.

Examples: `Controls.take_p_make_q` (computed by the kernel), `take_p_make_q_closed`, and
the negative `make_unbound_not_closed`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction Check EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
  (Firing Executable follow firstOrder executable_iff_run follow_eq_last)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (publish publish_present survivors)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## Knowing a store -/

/-- The label of an occurrence under a solution. -/
def resolve (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (label : O → Atom)
    (o : O) : Atom :=
  SubstitutionAlgebra.subst ρ (label o)

/-- Rows and knowledge that know a store: under every solution of the knowledge the rows'
labels are the store's atoms, in order. -/
structure Knows (label : O → Atom) (K : EquationStore Atom) (n : Nat) (rows : List O)
    (s : Store) : Prop where
  distinct : rows.Nodup
  consistent : atomAction.Consistent K
  resolved : ∀ ρ, atomAction.Models ρ K → rows.map (resolve ρ label) = s
  ground : ∀ a ∈ s, isGroundAtom a = true
  knowledgeBelow : ∀ e ∈ K, TagsBelow n e.1 ∧ TagsBelow n e.2
  labelsBelow : ∀ o ∈ rows, TagsBelow n (label o)

omit [DecidableEq O] in
/-- A ground store represented by its rows is known with no knowledge. -/
theorem knows_of_represents {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (ground : ∀ a ∈ s, isGroundAtom a = true) :
    Knows label [] 0 rows s := by
  have groundLabel : ∀ o ∈ rows, isGroundAtom (label o) = true := fun o present =>
    ground _ (by rw [← rep.labels]; exact List.mem_map_of_mem present)
  refine ⟨rep.distinct,
    ⟨Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty, by intro e member; simp at member⟩,
    ?_, ground, by intro e member; simp at member,
    fun o present => tagsBelow_of_ground 0 (groundLabel o present)⟩
  intro ρ _
  rw [← rep.labels]
  refine List.map_congr_left fun o present => ?_
  exact Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
    (vars_of_ground _ (groundLabel o present))

/-- The rule instance of a transform that makes its template's parts. -/
def madeRule (pats : Footprint) (absents : List Atom) (template : Atom) : RuleInstance Atom :=
  ⟨takes pats, reads pats, [], absents.map Check.absent, split template⟩

/-! ## What a fired branch provides, with its instances -/

/-- As `guarded_branch_fire_data`, with the branch's answers: what `emit` makes of the
bindings. -/
theorem guarded_branch_fire_out {label : O → Atom} {rows : List O} {s s' : Store}
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
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' ∧ out = emit σ := by
  obtain ⟨c, member, sel, rows', real, _, same, rep', _, answers⟩ := fire_publishes rep fired
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
  refine ⟨k.1, sel, rows', real, solvedHere,
    fun ρ each => walk_guided_kernel_agrees pats g fits kernelRow (agrees_nil ρ) each,
    none, same, rep', ?_⟩
  rw [answers]
  simp [Candidate.instances]

/-! ## One firing that makes -/

/-- **A branch that fires and makes its instances is a valid firing of the step from
knowledge, and what it leaves knows the model's store.** -/
theorem made_fire_step {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {K : EquationStore Atom} {n : Nat} {rows : List O} {s s' : Store}
    (knows : Knows label K n rows s) {pats g : Footprint} {absents : List Atom}
    {template : Atom} (fits : Fits pats g) (closed : Closed pats template) {out : Answers}
    (fired : LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩
      (instances template) = some (s', out)) :
    ∃ (sel : Selection O) (rows' : List O),
      sel.Valid atomAction label ((madeRule pats absents template).map (rename n))
        ⟨K, rows.toFinset⟩ ∧
      Knows label (sel.problem label ((madeRule pats absents template).map (rename n))
        ⟨K, rows.toFinset⟩) (n + 1) rows' (s' ++ out) ∧
      rows'.toFinset =
        Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire
          rows.toFinset (sel.commit (T := Atom)) := by
  obtain ⟨ρ₀, models₀⟩ := knows.consistent
  have rep₀ : Represents (resolve ρ₀ label) rows s := ⟨knows.distinct, knows.resolved ρ₀ models₀⟩
  obtain ⟨σ, sel₀, mid, real, solved, agreesOf, none, published, represented, outEq⟩ :=
    guarded_branch_fire_out rep₀ fits fired
  have plain := selection_valid_of_solved solved real
  have modes := forall₂_modes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
  -- the value of a present occurrence: ground, and the same under every solution of `K`
  have groundValue : ∀ o ∈ rows, isGroundAtom (resolve ρ₀ label o) = true := fun o present =>
    knows.ground _ (by rw [← rep₀.labels]; exact List.mem_map_of_mem present)
  have sameValue : ∀ ρ, atomAction.Models ρ K → ∀ o ∈ rows,
      resolve ρ label o = resolve ρ₀ label o := fun ρ models =>
    List.map_inj_left.mp ((knows.resolved ρ models).trans (knows.resolved ρ₀ models₀).symm)
  have fixedValue : ∀ (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst), ∀ o ∈ rows,
      SubstitutionAlgebra.subst ρ (resolve ρ₀ label o) = resolve ρ₀ label o :=
    fun ρ o present =>
      Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
        (vars_of_ground _ (groundValue o present))
  have takeLength : ((takes pats).map (rename n)).length = sel₀.taken.length := by
    rw [List.length_map]; exact plain.take_length
  have readLength : ((reads pats).map (rename n)).length = sel₀.read.length := by
    rw [List.length_map]; exact plain.read_length
  have takeLocal : List.Forall₂
      (fun p o => SubstitutionAlgebra.subst (solution σ) p = resolve ρ₀ label o)
      (takes pats) sel₀.taken := by
    have each := forall₂_takes (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
    rw [← real.taken_labels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution σ) a =
        SubstitutionAlgebra.subst (solution σ) (resolve ρ₀ label o) := equal
    rw [same, fixedValue _ o (real.taken_present o member)]
  have readLocal : List.Forall₂
      (fun p o => SubstitutionAlgebra.subst (solution σ) p = resolve ρ₀ label o)
      (reads pats) sel₀.read := by
    have each := forall₂_reads (R := fun p b => atomAction.Solves (solution σ) (p, b)) solved
    rw [← real.read_labels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution σ) a =
        SubstitutionAlgebra.subst (solution σ) (resolve ρ₀ label o) := equal
    rw [same, fixedValue _ o (real.read_present o member)]
  -- the occurrences made
  obtain ⟨made, madeDistinct, madeFresh, madeLabels⟩ :=
    exists_made supply ((split template).map (rename n)) rows.toFinset
  have madeOutside : ∀ o ∈ made, o ∉ rows := fun o member present =>
    madeFresh o member (List.mem_toFinset.mpr present)
  -- every solution of the firing's equations, untagged, agrees with the row's bindings
  have agreesOfModels : ∀ ρ,
      atomAction.Models ρ (Selection.equations label ((takes pats).map (rename n)) sel₀.taken) →
      atomAction.Models ρ (Selection.equations label ((reads pats).map (rename n)) sel₀.read) →
      atomAction.Models ρ K → Agrees (untagged ρ n) σ := by
    intro ρ takeModels readModels models
    have takeSolved : List.Forall₂
        (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (takes pats) (takes g) := by
      rw [← real.taken_labels]
      have each := List.forall₂_map_left_iff.mp
        ((Selection.models_equations_iff atomAction ρ label takeLength).mp takeModels)
      refine forall₂_map_of_mem each ?_
      intro a o member equal
      have same : SubstitutionAlgebra.subst ρ (rename n a) = resolve ρ label o := equal
      rw [sameValue ρ models o (real.taken_present o member)] at same
      exact subst_untagged_of_rename ρ n a _ same (groundValue o (real.taken_present o member))
    have readSolved : List.Forall₂
        (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (reads pats) (reads g) := by
      rw [← real.read_labels]
      have each := List.forall₂_map_left_iff.mp
        ((Selection.models_equations_iff atomAction ρ label readLength).mp readModels)
      refine forall₂_map_of_mem each ?_
      intro a o member equal
      have same : SubstitutionAlgebra.subst ρ (rename n a) = resolve ρ label o := equal
      rw [sameValue ρ models o (real.read_present o member)] at same
      exact subst_untagged_of_rename ρ n a _ same (groundValue o (real.read_present o member))
    exact agreesOf _ (forall₂_of_takes_reads modes takeSolved readSolved)
  have validity : (⟨sel₀.taken, sel₀.read, made⟩ : Selection O).Valid atomAction label
      ((madeRule pats absents template).map (rename n)) ⟨K, rows.toFinset⟩ := by
    refine ⟨real.taken_distinct, madeDistinct, takeLength, readLength, madeLabels, ?_, ?_, ?_⟩
    · exact
        { taken_subset := fun o member =>
            List.mem_toFinset.mpr (real.taken_present o (List.mem_toFinset.mp member))
          kept_subset := fun o member =>
            List.mem_toFinset.mpr (real.read_present o (List.mem_toFinset.mp member))
          apart := Finset.disjoint_left.mpr fun o taken kept =>
            real.apart o (List.mem_toFinset.mp kept) (List.mem_toFinset.mp taken)
          fresh := Finset.disjoint_left.mpr fun o inMade present =>
            madeFresh o (List.mem_toFinset.mp inMade) present
          queries_hold := by simp [Selection.commit] }
    · refine ⟨withLocal ρ₀ n (solution σ), ?_⟩
      simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil, List.append_nil,
        SubstitutionAction.models_append]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro e member
        have old : SubstitutionAlgebra.subst ρ₀ e.1 = SubstitutionAlgebra.subst ρ₀ e.2 :=
          models₀ e member
        show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) e.1 =
          SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) e.2
        rw [subst_withLocal_of_tagsBelow ρ₀ (solution σ) (knows.knowledgeBelow e member).1,
          subst_withLocal_of_tagsBelow ρ₀ (solution σ) (knows.knowledgeBelow e member).2]
        exact old
      · refine (Selection.models_equations_iff atomAction _ label takeLength).mpr ?_
        refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem takeLocal ?_)
        intro p o member here
        show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) (rename n p) =
          SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) (label o)
        rw [subst_withLocal_rename ρ₀ (solution σ) n p _ here
            (groundValue o (real.taken_present o member)),
          subst_withLocal_of_tagsBelow ρ₀ (solution σ)
            (knows.labelsBelow o (real.taken_present o member))]
        rfl
      · refine (Selection.models_equations_iff atomAction _ label readLength).mpr ?_
        refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem readLocal ?_)
        intro p o member here
        show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) (rename n p) =
          SubstitutionAlgebra.subst (withLocal ρ₀ n (solution σ)) (label o)
        rw [subst_withLocal_rename ρ₀ (solution σ) n p _ here
            (groundValue o (real.read_present o member)),
          subst_withLocal_of_tagsBelow ρ₀ (solution σ)
            (knows.labelsBelow o (real.read_present o member))]
        rfl
    · intro check member ρ models
      change check ∈ (absents.map Check.absent).map (Check.map (rename n)) at member
      obtain ⟨plainCheck, inChecks, rfl⟩ := List.mem_map.mp member
      obtain ⟨p, inside, rfl⟩ := List.mem_map.mp inChecks
      have all : atomAction.Models ρ
          ((⟨sel₀.taken, sel₀.read, made⟩ : Selection O).problem label
            ((madeRule pats absents template).map (rename n)) ⟨K, rows.toFinset⟩) := models
      simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil,
        List.append_nil, SubstitutionAction.models_append] at all
      have agrees := agreesOfModels ρ all.1.2 all.2 all.1.1
      have own := absent_check_holds rep₀ knows.ground (none p inside) agrees
      show ∀ o ∈ rows.toFinset,
        ¬ atomAction.E (atomAction.apply ρ (rename n p)) (atomAction.apply ρ (label o))
      intro o present equal
      have inRows : o ∈ rows := List.mem_toFinset.mp present
      have same : SubstitutionAlgebra.subst ρ (rename n p) = resolve ρ label o := equal
      rw [sameValue ρ all.1.1 o inRows] at same
      have untaggedSame := subst_untagged_of_rename ρ n p _ same (groundValue o inRows)
      refine own o present ?_
      show SubstitutionAlgebra.subst (untagged ρ n) p =
        SubstitutionAlgebra.subst (untagged ρ n) (resolve ρ₀ label o)
      rw [untaggedSame, fixedValue _ o inRows]
  -- what the firing leaves
  have midInRows : ∀ o ∈ mid, o ∈ rows := by
    intro o member
    have inPublished := published.subset member
    simp only [publish, real.made_none, List.append_nil, survivors, List.mem_filter] at inPublished
    exact inPublished.1
  have midPresent : mid.toFinset = rows.toFinset \ sel₀.taken.toFinset := by
    rw [List.toFinset_eq_of_perm _ _ published, publish_present]
    simp [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire,
      Selection.commit, real.made_none]
  have groundGuide : ∀ f ∈ g, isGroundAtom f.2 = true := fits.ground
  have outGround : ∀ a ∈ out, isGroundAtom a = true := by
    rw [outEq]
    exact instances_ground_of_closed closed solved groundGuide
  refine ⟨⟨sel₀.taken, sel₀.read, made⟩, mid ++ made, validity, ?_, ?_⟩
  · refine ⟨?_, validity.consistent, ?_, ?_, ?_, ?_⟩
    · exact List.Nodup.append represented.distinct madeDistinct
        fun o inMid inMade => madeOutside o inMade (midInRows o inMid)
    · intro ρ models
      have all : atomAction.Models ρ
          ((⟨sel₀.taken, sel₀.read, made⟩ : Selection O).problem label
            ((madeRule pats absents template).map (rename n)) ⟨K, rows.toFinset⟩) := models
      simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil,
        List.append_nil, SubstitutionAction.models_append] at all
      have agrees := agreesOfModels ρ all.1.2 all.2 all.1.1
      rw [List.map_append]
      congr 1
      · rw [← represented.labels]
        exact List.map_congr_left fun o member => sameValue ρ all.1.1 o (midInRows o member)
      · have asLabels : made.map (resolve ρ label) =
            (made.map label).map (SubstitutionAlgebra.subst ρ) := by
          rw [List.map_map]
          rfl
        rw [asLabels, madeLabels, List.map_map, outEq]
        refine List.map_congr_left fun t inTemplate => ?_
        have bound := boundGround_of_closed closed solved groundGuide t inTemplate
        have value : SubstitutionAlgebra.subst (untagged ρ n) t = applySubst σ t := by
          rw [subst_eq_of_agrees agrees bound, applySubst_eq_subst]
        show SubstitutionAlgebra.subst ρ (rename n t) = applySubst σ t
        refine subst_rename_of_untagged ρ n t _ value ?_
        rw [applySubst_eq_subst]
        exact ground_subst_of_boundGround _ _ bound
    · intro a member
      rcases List.mem_append.mp member with old | new
      · exact fire_keeps_ground knows.ground fired a old
      · exact outGround a new
    · intro e member
      simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil,
        List.append_nil, List.mem_append] at member
      rcases member with (old | taken) | read
      · exact ⟨(knows.knowledgeBelow e old).1.mono (Nat.le_succ n),
          (knows.knowledgeBelow e old).2.mono (Nat.le_succ n)⟩
      · obtain ⟨p', inP, o, inO, rfl⟩ := mem_equations taken
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp inP
        exact ⟨tagsBelow_rename n p,
          (knows.labelsBelow o (real.taken_present o inO)).mono (Nat.le_succ n)⟩
      · obtain ⟨p', inP, o, inO, rfl⟩ := mem_equations read
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp inP
        exact ⟨tagsBelow_rename n p,
          (knows.labelsBelow o (real.read_present o inO)).mono (Nat.le_succ n)⟩
    · intro o member
      rcases List.mem_append.mp member with old | new
      · exact (knows.labelsBelow o (midInRows o old)).mono (Nat.le_succ n)
      · have isLabel : label o ∈ (split template).map (rename n) := by
          rw [← madeLabels]
          exact List.mem_map_of_mem new
        obtain ⟨t, _, same⟩ := List.mem_map.mp isLabel
        rw [← same]
        exact tagsBelow_rename n t
  · rw [List.toFinset_append, midPresent]
    simp [Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire,
      Selection.commit]

/-! ## The whole call -/

/-- The fold of the branches of a transform that makes its instances is an executable word
of the step, and what the word leaves knows the store the fold leaves. -/
theorem made_fold_executable {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    (pats : Footprint) (absents : List Atom) (template : Atom)
    (closed : Closed pats template) :
    ∀ (guides : List Footprint), (∀ g ∈ guides, Fits pats g) →
      ∀ (acc : List Nat × Store) (rows : List O) (K : EquationStore Atom) (n : Nat),
        Knows label K n rows acc.2 →
        ∃ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
          (rows' : List O) (K' : EquationStore Atom) (n' : Nat),
          Executable atomAction label ⟨K, rows.toFinset⟩ word ∧
          follow label ⟨K, rows.toFinset⟩ word = ⟨K', rows'.toFinset⟩ ∧
          Knows label K' n' rows'
            (guides.foldl
              (branchStep intoStore ⟨kernelOf pats ++ absentsOf absents, [], none⟩
                (instances template)) acc).2 ∧
          (∀ f ∈ word, ∃ m, f.rule = (madeRule pats absents template).map (rename m) ∧
            f.queries = []) ∧
          word.length ≤ guides.length
  | [], _, acc, rows, K, n, knows =>
      ⟨[], rows, K, n, knows.consistent, rfl, knows, by simp, Nat.le_refl _⟩
  | g :: guides, fits, acc, rows, K, n, knows => by
      have later : ∀ g' ∈ guides, Fits pats g' := fun g' member =>
        fits g' (List.mem_cons_of_mem _ member)
      cases fired : LibTransform.fire acc.2 g
          ⟨kernelOf pats ++ absentsOf absents, [], none⟩ (instances template) with
      | none =>
          have same : branchStep intoStore ⟨kernelOf pats ++ absentsOf absents, [], none⟩
              (instances template) acc g = acc := by
            simp [branchStep, fired]
          obtain ⟨word, rows', K', n', exec, ends, knows', rules, len⟩ :=
            made_fold_executable supply pats absents template closed guides later acc rows K n
              knows
          refine ⟨word, rows', K', n', exec, ends, ?_, rules, Nat.le_succ_of_le len⟩
          rw [List.foldl_cons, same]
          exact knows'
      | some result =>
          obtain ⟨s', out⟩ := result
          have next : branchStep intoStore ⟨kernelOf pats ++ absentsOf absents, [], none⟩
              (instances template) acc g = (acc.1 ++ [out.length], s' ++ out) := by
            simp [branchStep, fired, intoStore]
          obtain ⟨sel, mid, valid, knowsNext, present⟩ :=
            made_fire_step supply knows (fits g (List.mem_cons_self ..)) closed fired
          obtain ⟨word, rows', K', n', exec, ends, knows', rules, len⟩ :=
            made_fold_executable supply pats absents template closed guides later
              (acc.1 ++ [out.length], s' ++ out) mid
              (sel.problem label ((madeRule pats absents template).map (rename n))
                ⟨K, rows.toFinset⟩) (n + 1) knowsNext
          have result :
              (Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
                ((madeRule pats absents template).map (rename n), sel)).result label
                  ⟨K, rows.toFinset⟩ =
                ⟨sel.problem label ((madeRule pats absents template).map (rename n))
                  ⟨K, rows.toFinset⟩, mid.toFinset⟩ := by
            rw [present]
            rfl
          refine ⟨Firing.ofPlain ((madeRule pats absents template).map (rename n), sel) :: word,
            rows', K', n', ?_, ?_, ?_, ?_, Nat.succ_le_succ len⟩
          · refine ⟨(Firing.valid_ofPlain_iff atomAction label _ _).mpr valid, ?_⟩
            rw [result]
            exact exec
          · show follow label
              ((Firing.ofPlain (S := Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
                ((madeRule pats absents template).map (rename n), sel)).result label
                  ⟨K, rows.toFinset⟩) word = ⟨K', rows'.toFinset⟩
            rw [result]
            exact ends
          · rw [List.foldl_cons, next]
            exact knows'
          · intro f member
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨n, rfl, rfl⟩
            · exact rules f member

/-- **A transform that makes atoms is a run of the first-order step.** On a ground store
represented by `rows`, with a supply of fresh occurrences for every label, the call
`(transform SPACE SOURCES TEMPLATE SPACE)` of a kernel of reads and takes guarded by
absences, with a template whose variables the kernel binds, is a run of
`firstOrder atomAction label` from the configuration with the rows' occurrences and no
knowledge. Each firing takes and reads the occurrences of its branch and makes fresh
occurrences labelled with the template's parts in its own variables. At the end of the
run, the knowledge is consistent and under every solution of it the labels of the last
rows are the atoms of the store the call leaves, in order. -/
theorem made_transform_is_run {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (pats : Footprint) (absents : List Atom) (template : Atom)
    (closed : Closed pats template) :
    ∃ (run : (firstOrder atomAction label).Run (⟨[], rows.toFinset⟩ : Configuration Atom O))
      (rows' : List O) (n : Nat),
      run.last.present = rows'.toFinset ∧
      Knows label run.last.equations n rows'
        ((transformInto ⟨kernelOf pats ++ absentsOf absents, [], none⟩ template s).drain).2 := by
  obtain ⟨word, rows', K', n', exec, ends, knows', _, _⟩ :=
    made_fold_executable supply pats absents template closed _
      (fun g member => guarded_proposal_fits ground member) ([], s) rows [] 0
      (knows_of_represents rep ground)
  obtain ⟨run, isWord, _⟩ := (executable_iff_run atomAction label _ word).mp exec
  have last : run.last = ⟨K', rows'.toFinset⟩ := by
    rw [← follow_eq_last atomAction label run, isWord]
    exact ends
  refine ⟨run, rows', n', by rw [last], ?_⟩
  rw [last, transformInto, transformWith_drain]
  exact knows'

namespace Controls

/-- A rule that takes `(p x)` and makes `(q x)`: on `[(p a), b]` its one branch fires,
answers the count `1`, and leaves `b` followed by `(q a)`. -/
theorem take_p_make_q :
    (transformInto
      ⟨kernelOf [(Mode.take, .expression [.symbol "p", .var "x"])] ++ absentsOf [], [], none⟩
      (.expression [.symbol "q", .var "x"]) [.expression [.symbol "p", a], b]).drain =
      ([1], [b, .expression [.symbol "q", a]]) := by
  decide

/-- Its template is closed in its kernel. -/
theorem take_p_make_q_closed :
    Closed [(Mode.take, .expression [.symbol "p", .var "x"])]
      (.expression [.symbol "q", .var "x"]) := by
  intro t inTemplate v member
  have single : split (.expression [.symbol "q", .var "x"]) =
      [.expression [.symbol "q", .var "x"]] := by decide
  rw [single, List.mem_singleton] at inTemplate
  subst inTemplate
  have isX : v = "x" := by
    have vars : SubstitutionAlgebra.vars (.expression [.symbol "q", .var "x"]) = ["x"] := by
      decide
    rw [vars, List.mem_singleton] at member
    exact member
  subst isX
  exact ⟨_, List.mem_singleton_self _, by decide⟩

/-- A template with a variable the kernel does not bind is not closed in it. -/
theorem make_unbound_not_closed :
    ¬ Closed [(Mode.take, .expression [.symbol "p", .var "x"])]
      (.expression [.symbol "q", .var "y"]) := by
  intro closed
  obtain ⟨e, inPats, inVars⟩ := closed (.expression [.symbol "q", .var "y"])
    (by decide) "y" (by decide)
  simp only [List.mem_singleton] at inPats
  subst inPats
  revert inVars
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
