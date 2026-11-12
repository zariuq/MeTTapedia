import Mettapedia.Languages.MeTTa.PeTTa.LibTransformMakes

/-!
# The model fires whenever the step admits: halting in the step's terms

`LibTransformMakes.made_fire_step` is soundness: a branch that fires is a valid firing of
the step. This module proves the converse for the same rules, so that "nothing fired" is
evidence about the step and not only about the model.

* `weave`, `weave_spec`: the footprint in conjunct order, from the atoms taken and the
  atoms read.
* `walk_kernel_complete`, `walk_guided_kernel_complete`: where a solution makes the
  kernel's patterns equal to stored atoms, the walk (and the guided walk) has the row with
  exactly those atoms, and the solution agrees with the row's bindings.
* `absent_of_checks`: if the step's absence checks hold at every solution of a valid
  firing's equations, then no stored atom matches an absent pattern under the row's
  bindings. Otherwise the match would extend to a solution at which a check fails.
* `made_valid_fires`: **if the step admits a firing of the made rule at a known
  configuration, the model's call fires a branch.**
* `made_admitted_iff_fires`: the rule is admitted there exactly when some branch of the
  call fires; `made_idle_refuses`: where every branch fires nothing, no selection is valid.
* `Quiescent`, `quiescent_iff_idle`: for a program, a list of such rules: no rule of it is
  admitted exactly when every branch of every rule's call fires nothing; and then a call of
  any of its rules leaves the store as it is (`idle_drain`).

Scope as in `LibTransformMakes`: one space, ground store, `absent` of one pattern, a
template closed in the kernel (needed for soundness only).

Examples: `Controls.pToQ_idle` and the negative `Controls.pToQ_not_idle`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst isGroundAtom applySubst matchAtom MatchAtomRel matchAtom_complete
    matchAtom_lookupExtends matchAtom_applySubst_ground)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction Check EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst)
open LibTransform

variable {O : Type} [DecidableEq O]

/-! ## The footprint in conjunct order -/

/-- The footprint of a kernel from the atoms its takes and its reads picked. -/
def weave : Footprint → List Atom → List Atom → Footprint
  | [], _, _ => []
  | (.take, _) :: pats, b :: ts, rs => (.take, b) :: weave pats ts rs
  | (.read, _) :: pats, ts, b :: rs => (.read, b) :: weave pats ts rs
  | (.take, _) :: _, [], _ => []
  | (.read, _) :: _, _, [] => []

theorem weave_spec {R : Atom → Atom → Prop} :
    ∀ (pats : Footprint) {ts rs : List Atom},
      List.Forall₂ R (takes pats) ts → List.Forall₂ R (reads pats) rs →
      List.Forall₂ (fun e f => e.1 = f.1 ∧ R e.2 f.2) pats (weave pats ts rs) ∧
        takes (weave pats ts rs) = ts ∧ reads (weave pats ts rs) = rs
  | [], ts, rs, taken, read => by
      have noTakes : ts = [] := by cases taken; rfl
      have noReads : rs = [] := by cases read; rfl
      subst noTakes noReads
      exact ⟨List.Forall₂.nil, rfl, rfl⟩
  | (.take, p) :: pats, ts, rs, taken, read => by
      have shapeT : takes ((Mode.take, p) :: pats) = p :: takes pats := by simp [takes]
      have shapeR : reads ((Mode.take, p) :: pats) = reads pats := by simp [reads]
      rw [shapeT] at taken
      rw [shapeR] at read
      cases taken with
      | cons head tail =>
          obtain ⟨woven, tk, rd⟩ := weave_spec pats tail read
          refine ⟨List.Forall₂.cons ⟨rfl, head⟩ woven, ?_, ?_⟩
          · simp only [weave, takes, List.filterMap_cons]
            exact congrArg _ tk
          · simp only [weave, reads, List.filterMap_cons]
            exact rd
  | (.read, p) :: pats, ts, rs, taken, read => by
      have shapeT : takes ((Mode.read, p) :: pats) = takes pats := by simp [takes]
      have shapeR : reads ((Mode.read, p) :: pats) = p :: reads pats := by simp [reads]
      rw [shapeT] at taken
      rw [shapeR] at read
      cases read with
      | cons head tail =>
          obtain ⟨woven, tk, rd⟩ := weave_spec pats taken tail
          refine ⟨List.Forall₂.cons ⟨rfl, head⟩ woven, ?_, ?_⟩
          · simp only [weave, takes, List.filterMap_cons]
            exact tk
          · simp only [weave, reads, List.filterMap_cons]
            exact congrArg _ rd

/-! ## The walk has every row a solution describes -/

/-- Where a solution that agrees with the bindings so far makes each pattern equal to a
stored atom, the kernel's walk has the row that picks exactly those atoms, and the
solution agrees with the row's bindings. -/
theorem walk_kernel_complete {s : Store} {firing : Bool}
    {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst} :
    ∀ (pats fp : Footprint) {σ : Subst}, Agrees ρ σ →
      List.Forall₂ (fun e f => e.1 = f.1 ∧ SubstitutionAlgebra.subst ρ e.2 = f.2) pats fp →
      (∀ f ∈ fp, f.2 ∈ s) →
      ∃ w ∈ walk s firing σ (kernelOf pats), w.2 = fp ∧ Agrees ρ w.1
  | [], [], σ, agrees, _, _ => ⟨(σ, []), by simp [kernelOf, walk], rfl, agrees⟩
  | [], _ :: _, _, _, related, _ => by cases related
  | _ :: _, [], _, _, related, _ => by cases related
  | (m, p) :: pats, (m', b) :: fp, σ, agrees, related, stored => by
      cases related with
      | cons head rest =>
          obtain ⟨sameMode, solved⟩ := head
          have sameMode' : m = m' := sameMode
          subst sameMode'
          have solved' : SubstitutionAlgebra.subst ρ p = b := solved
          obtain ⟨τ, rel⟩ := rel_of_solution ρ p σ agrees
          rw [solved'] at rel
          have picked : (τ, b) ∈ matchesIn s σ p :=
            mem_matchesIn.mpr ⟨stored _ (List.mem_cons_self ..), matchAtom_complete rel⟩
          obtain ⟨v, later, same, agrees'⟩ :=
            walk_kernel_complete pats fp (rel_agrees rel agrees solved') rest
              (fun f member => stored f (List.mem_cons_of_mem _ member))
          refine ⟨(v.1, (m, b) :: v.2), ?_, by simp [same], agrees'⟩
          exact (mem_walk_pat (m := m) (p := p) (cs := kernelOf pats)).mpr
            ⟨(τ, b), picked, v, later, rfl⟩

/-- The same for the kernel guided by the footprint itself. -/
theorem walk_guided_kernel_complete {s : Store} {firing : Bool}
    {ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst} :
    ∀ (pats g : Footprint), Fits pats g → ∀ {σ : Subst}, Agrees ρ σ →
      List.Forall₂ (fun e f => SubstitutionAlgebra.subst ρ e.2 = f.2) pats g →
      (∀ f ∈ g, f.2 ∈ s) →
      ∃ w ∈ walk s firing σ (guided (kernelOf pats) g), w.2 = g ∧ Agrees ρ w.1
  | [], [], _, σ, agrees, _, _ => ⟨(σ, []), by simp [kernelOf, guided, walk], rfl, agrees⟩
  | [], _ :: _, fits, _, _, _, _ => by have := fits.modes; simp at this
  | _ :: _, [], fits, _, _, _, _ => by have := fits.modes; simp at this
  | (m, p) :: pats, (use, a) :: g, fits, σ, agrees, related, stored => by
      have rest : Fits pats g :=
        ⟨by have := fits.modes; simp only [List.map_cons, List.cons.injEq] at this; exact this.2,
          fun e inside => fits.ground e (List.mem_cons_of_mem _ inside)⟩
      have groundA : isGroundAtom a = true := fits.ground (use, a) (List.mem_cons_self ..)
      cases related with
      | cons head tail =>
          have solved' : SubstitutionAlgebra.subst ρ p = a := head
          obtain ⟨τ, rel⟩ := rel_of_solution ρ p σ agrees
          rw [solved'] at rel
          have matched : matchAtom σ p a = some τ := matchAtom_complete rel
          obtain ⟨v, later, same, agrees'⟩ :=
            walk_guided_kernel_complete pats g rest (rel_agrees rel agrees solved') tail
              (fun f member => stored f (List.mem_cons_of_mem _ member))
          have shape : guided (kernelOf ((m, p) :: pats)) ((use, a) :: g) =
              Conj.pat use a :: Conj.as p a :: guided (kernelOf pats) g := rfl
          refine ⟨(v.1, (use, a) :: v.2), ?_, by simp [same], agrees'⟩
          rw [shape]
          refine mem_walk_pat.mpr ⟨(σ, a), ?_, v, ?_, rfl⟩
          · exact (mem_matchesIn_ground groundA).mpr ⟨rfl, stored _ (List.mem_cons_self ..)⟩
          · simp only [walk, matched]
            exact later

/-! ## From the step's checks to the model's absences -/

/-- **A valid firing's absences hold in the model.** Let a selection be valid for the made
rule at a known configuration, and let `σ` be bindings every extension of which solves the
kernel's patterns against the selected values. Then no stored atom matches an absent
pattern under `σ`: a match would extend `σ` to a solution of the firing's equations at
which the step's absence check fails. -/
theorem absent_of_checks {label : O → Atom} {K : EquationStore Atom} {n : Nat}
    {rows : List O} {s : Store} (knows : Knows label K n rows s)
    {ρ₀ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst}
    (models₀ : atomAction.Models ρ₀ K)
    {pats : Footprint} {absents : List Atom} {template : Atom} {sel : Selection O}
    (valid : sel.Valid atomAction label ((madeRule pats absents template).map (rename n))
      ⟨K, rows.toFinset⟩)
    {σ : Subst} {fp : Footprint}
    (takeLabels : sel.taken.map (resolve ρ₀ label) = takes fp)
    (readLabels : sel.read.map (resolve ρ₀ label) = reads fp)
    (solvesAll : ∀ τ : Subst, Subst.lookupExtends τ σ →
      List.Forall₂ (fun e f => e.1 = f.1 ∧ atomAction.Solves (solution τ) (e.2, f.2)) pats fp) :
    ∀ p ∈ absents, matchesIn s σ p = [] := by
  intro p inside
  refine List.eq_nil_iff_forall_not_mem.mpr ?_
  rintro ⟨τ, b⟩ found
  obtain ⟨stored, matched⟩ := mem_matchesIn.mp found
  have ext : Subst.lookupExtends τ σ := matchAtom_lookupExtends matched
  have groundB : isGroundAtom b = true := knows.ground b stored
  -- present occurrences: their values under the chosen solution
  have inRowsTaken : ∀ o ∈ sel.taken, o ∈ rows := fun o member =>
    List.mem_toFinset.mp (valid.occurrences.taken_subset (List.mem_toFinset.mpr member))
  have inRowsRead : ∀ o ∈ sel.read, o ∈ rows := fun o member =>
    List.mem_toFinset.mp (valid.occurrences.kept_subset (List.mem_toFinset.mpr member))
  have groundValue : ∀ o ∈ rows, isGroundAtom (resolve ρ₀ label o) = true := fun o present =>
    knows.ground _ (by rw [← knows.resolved ρ₀ models₀]; exact List.mem_map_of_mem present)
  have fixedValue : ∀ (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst), ∀ o ∈ rows,
      SubstitutionAlgebra.subst ρ (resolve ρ₀ label o) = resolve ρ₀ label o :=
    fun ρ o present =>
      Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_of_vars_eq_nil _ _
        (vars_of_ground _ (groundValue o present))
  have takeLength : ((takes pats).map (rename n)).length = sel.taken.length := valid.take_length
  have readLength : ((reads pats).map (rename n)).length = sel.read.length := valid.read_length
  have solved := solvesAll τ ext
  have takeLocal : List.Forall₂
      (fun p o => SubstitutionAlgebra.subst (solution τ) p = resolve ρ₀ label o)
      (takes pats) sel.taken := by
    have each := forall₂_takes (R := fun p b => atomAction.Solves (solution τ) (p, b)) solved
    rw [← takeLabels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution τ) a =
        SubstitutionAlgebra.subst (solution τ) (resolve ρ₀ label o) := equal
    rw [same, fixedValue _ o (inRowsTaken o member)]
  have readLocal : List.Forall₂
      (fun p o => SubstitutionAlgebra.subst (solution τ) p = resolve ρ₀ label o)
      (reads pats) sel.read := by
    have each := forall₂_reads (R := fun p b => atomAction.Solves (solution τ) (p, b)) solved
    rw [← readLabels] at each
    refine forall₂_of_map_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst (solution τ) a =
        SubstitutionAlgebra.subst (solution τ) (resolve ρ₀ label o) := equal
    rw [same, fixedValue _ o (inRowsRead o member)]
  -- the solution at which the check would fail
  have models : atomAction.Models (withLocal ρ₀ n (solution τ))
      (sel.problem label ((madeRule pats absents template).map (rename n))
        ⟨K, rows.toFinset⟩) := by
    simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil, List.append_nil,
      SubstitutionAction.models_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro e member
      have old : SubstitutionAlgebra.subst ρ₀ e.1 = SubstitutionAlgebra.subst ρ₀ e.2 :=
        models₀ e member
      show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) e.1 =
        SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) e.2
      rw [subst_withLocal_of_tagsBelow ρ₀ (solution τ) (knows.knowledgeBelow e member).1,
        subst_withLocal_of_tagsBelow ρ₀ (solution τ) (knows.knowledgeBelow e member).2]
      exact old
    · refine (Selection.models_equations_iff atomAction _ label takeLength).mpr ?_
      refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem takeLocal ?_)
      intro q o member here
      show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (rename n q) =
        SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (label o)
      rw [subst_withLocal_rename ρ₀ (solution τ) n q _ here
          (groundValue o (inRowsTaken o member)),
        subst_withLocal_of_tagsBelow ρ₀ (solution τ)
          (knows.labelsBelow o (inRowsTaken o member))]
      rfl
    · refine (Selection.models_equations_iff atomAction _ label readLength).mpr ?_
      refine List.forall₂_map_left_iff.mpr (forall₂_imp_mem readLocal ?_)
      intro q o member here
      show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (rename n q) =
        SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (label o)
      rw [subst_withLocal_rename ρ₀ (solution τ) n q _ here
          (groundValue o (inRowsRead o member)),
        subst_withLocal_of_tagsBelow ρ₀ (solution τ)
          (knows.labelsBelow o (inRowsRead o member))]
      rfl
  -- an occurrence whose value is the matched atom
  have inImage : b ∈ rows.map (resolve ρ₀ label) := by
    rw [knows.resolved ρ₀ models₀]; exact stored
  obtain ⟨o, present, isValue⟩ := List.mem_map.mp inImage
  have check := valid.checks (Check.map (rename n) (Check.absent p))
    (by
      change Check.map (rename n) (Check.absent p) ∈
        (absents.map Check.absent).map (Check.map (rename n))
      exact List.mem_map_of_mem (List.mem_map_of_mem inside))
    (withLocal ρ₀ n (solution τ)) models
  have holds : ∀ o ∈ rows.toFinset,
      ¬ atomAction.E (atomAction.apply (withLocal ρ₀ n (solution τ)) (rename n p))
        (atomAction.apply (withLocal ρ₀ n (solution τ)) (label o)) := check
  refine holds o (List.mem_toFinset.mpr present) ?_
  have instanceOf : SubstitutionAlgebra.subst (solution τ) p = b := by
    rw [← applySubst_eq_subst]
    exact matchAtom_applySubst_ground σ p b τ matched groundB
  show SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (rename n p) =
    SubstitutionAlgebra.subst (withLocal ρ₀ n (solution τ)) (label o)
  rw [subst_withLocal_rename ρ₀ (solution τ) n p b instanceOf groundB,
    subst_withLocal_of_tagsBelow ρ₀ (solution τ) (knows.labelsBelow o present)]
  exact isValue.symm

/-! ## Completeness -/

/-- **If the step admits a firing of the made rule, the model fires a branch.** At a known
configuration, a selection valid for the made rule with variables tagged `n` gives a
proposal of the call whose branch fires. -/
theorem made_valid_fires {label : O → Atom} {K : EquationStore Atom} {n : Nat}
    {rows : List O} {s : Store} (knows : Knows label K n rows s)
    {pats : Footprint} {absents : List Atom} {template : Atom} {sel : Selection O}
    (valid : sel.Valid atomAction label ((madeRule pats absents template).map (rename n))
      ⟨K, rows.toFinset⟩) (emit : Subst → Answers) :
    ∃ g ∈ proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩,
      LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit ≠ none := by
  obtain ⟨ρ₀, models₀⟩ := knows.consistent
  have rep₀ : Represents (resolve ρ₀ label) rows s := ⟨knows.distinct, knows.resolved ρ₀ models₀⟩
  obtain ⟨ρ, models⟩ := valid.consistent
  have all : atomAction.Models ρ
      (sel.problem label ((madeRule pats absents template).map (rename n))
        ⟨K, rows.toFinset⟩) := models
  simp only [Selection.problem, RuleInstance.map, madeRule, List.map_nil, List.append_nil,
    SubstitutionAction.models_append] at all
  have inRowsTaken : ∀ o ∈ sel.taken, o ∈ rows := fun o member =>
    List.mem_toFinset.mp (valid.occurrences.taken_subset (List.mem_toFinset.mpr member))
  have inRowsRead : ∀ o ∈ sel.read, o ∈ rows := fun o member =>
    List.mem_toFinset.mp (valid.occurrences.kept_subset (List.mem_toFinset.mpr member))
  have groundValue : ∀ o ∈ rows, isGroundAtom (resolve ρ₀ label o) = true := fun o present =>
    knows.ground _ (by rw [← rep₀.labels]; exact List.mem_map_of_mem present)
  have sameValue : ∀ o ∈ rows, resolve ρ label o = resolve ρ₀ label o :=
    List.map_inj_left.mp ((knows.resolved ρ all.1.1).trans (knows.resolved ρ₀ models₀).symm)
  have takeLength : ((takes pats).map (rename n)).length = sel.taken.length := valid.take_length
  have readLength : ((reads pats).map (rename n)).length = sel.read.length := valid.read_length
  have takeSolved : List.Forall₂
      (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (takes pats)
      (sel.taken.map (resolve ρ₀ label)) := by
    have each := List.forall₂_map_left_iff.mp
      ((Selection.models_equations_iff atomAction ρ label takeLength).mp all.1.2)
    refine forall₂_map_of_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst ρ (rename n a) = resolve ρ label o := equal
    rw [sameValue o (inRowsTaken o member)] at same
    exact subst_untagged_of_rename ρ n a _ same (groundValue o (inRowsTaken o member))
  have readSolved : List.Forall₂
      (fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) (reads pats)
      (sel.read.map (resolve ρ₀ label)) := by
    have each := List.forall₂_map_left_iff.mp
      ((Selection.models_equations_iff atomAction ρ label readLength).mp all.2)
    refine forall₂_map_of_mem each ?_
    intro a o member equal
    have same : SubstitutionAlgebra.subst ρ (rename n a) = resolve ρ label o := equal
    rw [sameValue o (inRowsRead o member)] at same
    exact subst_untagged_of_rename ρ n a _ same (groundValue o (inRowsRead o member))
  obtain ⟨woven, takeLabels, readLabels⟩ := weave_spec pats takeSolved readSolved
  -- the footprint and its atoms
  have stored : ∀ f ∈ weave pats (sel.taken.map (resolve ρ₀ label))
      (sel.read.map (resolve ρ₀ label)), f.2 ∈ s := by
    rintro ⟨m, a⟩ member
    have valueStored : ∀ o ∈ rows, resolve ρ₀ label o ∈ s := fun o present => by
      rw [← rep₀.labels]; exact List.mem_map_of_mem present
    cases m with
    | take =>
        have inTakes : a ∈ takes (weave pats (sel.taken.map (resolve ρ₀ label))
            (sel.read.map (resolve ρ₀ label))) := mem_takes.mpr member
        rw [takeLabels] at inTakes
        obtain ⟨o, inTaken, rfl⟩ := List.mem_map.mp inTakes
        exact valueStored o (inRowsTaken o inTaken)
    | read =>
        have inReads : a ∈ reads (weave pats (sel.taken.map (resolve ρ₀ label))
            (sel.read.map (resolve ρ₀ label))) := mem_reads.mpr member
        rw [readLabels] at inReads
        obtain ⟨o, inRead, rfl⟩ := List.mem_map.mp inReads
        exact valueStored o (inRowsRead o inRead)
  have fits : Fits pats (weave pats (sel.taken.map (resolve ρ₀ label))
      (sel.read.map (resolve ρ₀ label))) :=
    ⟨forall₂_modes (R := fun p b => SubstitutionAlgebra.subst (untagged ρ n) p = b) woven,
      fun f member => knows.ground _ (stored f member)⟩
  have plainSolved : List.Forall₂ (fun e f => SubstitutionAlgebra.subst (untagged ρ n) e.2 = f.2)
      pats (weave pats (sel.taken.map (resolve ρ₀ label)) (sel.read.map (resolve ρ₀ label))) :=
    woven.imp fun _ _ both => both.2
  -- the proposal
  obtain ⟨w, walked, isFootprint, _⟩ :=
    walk_kernel_complete (s := s) (firing := false) pats _ (agrees_nil (untagged ρ n)) woven stored
  have absentAtProposal := absent_of_checks knows models₀ valid takeLabels.symm readLabels.symm
    (σ := w.1) (fun τ ext => by
      have := walk_kernel_solves knows.ground pats walked ext
      rw [isFootprint] at this
      exact this)
  have proposed : weave pats (sel.taken.map (resolve ρ₀ label))
      (sel.read.map (resolve ρ₀ label)) ∈
      proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩ := by
    refine mem_proposals.mpr ⟨w.1, ?_⟩
    rw [walk_append]
    refine List.mem_flatMap.mpr ⟨w, walked, List.mem_map.mpr ⟨(w.1, []), ?_, ?_⟩⟩
    · exact (mem_walk_absents absents).mpr ⟨rfl, absentAtProposal⟩
    · simp [isFootprint]
  refine ⟨_, proposed, ?_⟩
  -- its branch fires: the guided row is a candidate with a selection
  obtain ⟨k, guidedRow, isGuide, _⟩ :=
    walk_guided_kernel_complete (s := s) (firing := true) pats _ fits
      (agrees_nil (untagged ρ n)) plainSolved stored
  have absentAtFiring := absent_of_checks knows models₀ valid takeLabels.symm readLabels.symm
    (σ := k.1) (fun τ ext => by
      have := (walk_guided_kernel_solves pats _ fits guidedRow).2 ext
      rw [isGuide] at this
      exact this)
  intro refused
  have noCandidate := (fire_eq_none_iff_unrealized rep₀).mp refused
  refine noCandidate ⟨k.2 ++ [], [(k.1, [])]⟩ ?_ ⟨⟨sel.taken, sel.read, []⟩, ?_⟩
  · refine List.mem_map.mpr ⟨(k.1, k.2 ++ []), ?_, rfl⟩
    rw [guided_guarded pats _ absents fits, List.append_nil, walk_append]
    exact List.mem_flatMap.mpr ⟨k, guidedRow, List.mem_map.mpr
      ⟨(k.1, []), (mem_walk_absents absents).mpr ⟨rfl, absentAtFiring⟩, rfl⟩⟩
  · have footprint : (Candidate.footprint ⟨k.2 ++ [], [(k.1, [])]⟩) =
        weave pats (sel.taken.map (resolve ρ₀ label)) (sel.read.map (resolve ρ₀ label)) := by
      simp [Candidate.footprint, isGuide]
    rw [footprint]
    exact
      { taken_distinct := valid.take_distinct
        taken_present := inRowsTaken
        read_present := inRowsRead
        apart := fun o inRead inTaken =>
          Finset.disjoint_left.mp valid.occurrences.apart (List.mem_toFinset.mpr inTaken)
            (List.mem_toFinset.mpr inRead)
        taken_labels := takeLabels.symm
        read_labels := readLabels.symm
        made_none := rfl }

/-- Where every branch of the call fires nothing, no selection is valid for the rule. -/
theorem made_idle_refuses {label : O → Atom} {K : EquationStore Atom} {n : Nat}
    {rows : List O} {s : Store} (knows : Knows label K n rows s)
    {pats : Footprint} {absents : List Atom} {template : Atom} {emit : Subst → Answers}
    (idle : ∀ g ∈ proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩,
      LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩ emit = none) :
    ∀ sel : Selection O, ¬ sel.Valid atomAction label
      ((madeRule pats absents template).map (rename n)) ⟨K, rows.toFinset⟩ := by
  intro sel valid
  obtain ⟨g, member, fires⟩ := made_valid_fires knows valid emit
  exact fires (idle g member)

/-- **The step admits the made rule exactly when the model's call fires a branch.** -/
theorem made_admitted_iff_fires {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store}
    (knows : Knows label K n rows s) {pats : Footprint} {absents : List Atom}
    {template : Atom} (closed : Closed pats template) :
    (∃ sel : Selection O, sel.Valid atomAction label
        ((madeRule pats absents template).map (rename n)) ⟨K, rows.toFinset⟩) ↔
      ∃ g ∈ proposals s ⟨kernelOf pats ++ absentsOf absents, [], none⟩,
        LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩
          (instances template) ≠ none := by
  constructor
  · rintro ⟨sel, valid⟩
    exact made_valid_fires knows valid (instances template)
  · rintro ⟨g, member, fires⟩
    cases fired : LibTransform.fire s g ⟨kernelOf pats ++ absentsOf absents, [], none⟩
        (instances template) with
    | none => exact absurd fired fires
    | some result =>
        obtain ⟨s', out⟩ := result
        obtain ⟨sel, _, valid, _, _⟩ :=
          made_fire_step supply knows (guarded_proposal_fits knows.ground member) closed fired
        exact ⟨sel, valid⟩

/-! ## A program: halting in the step's terms -/

/-- A rule of a program: its kernel, its absences, its template. -/
structure MadeRule where
  pats : Footprint
  absents : List Atom
  template : Atom

/-- The sources of a rule. -/
def MadeRule.sources (r : MadeRule) : Sources := ⟨kernelOf r.pats ++ absentsOf r.absents, [], none⟩

/-- No rule of the program is admitted by the step at the configuration. -/
def Quiescent (label : O → Atom) (program : List MadeRule) (K : EquationStore Atom)
    (n : Nat) (rows : List O) : Prop :=
  ∀ r ∈ program, ∀ sel : Selection O, ¬ sel.Valid atomAction label
    ((madeRule r.pats r.absents r.template).map (rename n)) ⟨K, rows.toFinset⟩

/-- Every branch of every rule's call fires nothing. -/
def Idle (program : List MadeRule) (s : Store) : Prop :=
  ∀ r ∈ program, ∀ g ∈ proposals s r.sources,
    LibTransform.fire s g r.sources (instances r.template) = none

/-- **A program is quiescent in the step's terms exactly when it is idle in the model.**
Idleness is what a driver observes after a pass in which nothing fired; quiescence says no
rule instance of the program is admitted. -/
theorem quiescent_iff_idle {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store}
    (knows : Knows label K n rows s) (program : List MadeRule)
    (closed : ∀ r ∈ program, Closed r.pats r.template) :
    Quiescent label program K n rows ↔ Idle program s := by
  constructor
  · intro quiescent r member g proposed
    by_contra fires
    obtain ⟨sel, valid⟩ := (made_admitted_iff_fires supply knows (closed r member)).mpr
      ⟨g, proposed, fires⟩
    exact quiescent r member sel valid
  · intro idle r member
    exact made_idle_refuses knows (idle r member)

/-- An idle rule's call leaves the store as it is and answers nothing. -/
theorem idle_drain {s : Store} {r : MadeRule}
    (idle : ∀ g ∈ proposals s r.sources,
      LibTransform.fire s g r.sources (instances r.template) = none) :
    (transformInto r.sources r.template s).drain = ([], s) := by
  rw [transformInto, transformWith_drain]
  have step : ∀ (guides : List Footprint) (acc : List Nat × Store),
      (∀ g ∈ guides, LibTransform.fire acc.2 g r.sources (instances r.template) = none) →
      guides.foldl (branchStep intoStore r.sources (instances r.template)) acc = acc := by
    intro guides
    induction guides with
    | nil => intro acc _; rfl
    | cons g guides ih =>
        intro acc none
        have here : branchStep intoStore r.sources (instances r.template) acc g = acc := by
          simp [branchStep, none g (List.mem_cons_self ..)]
        rw [List.foldl_cons, here]
        exact ih acc fun g' member => none g' (List.mem_cons_of_mem _ member)
  exact step _ ([], s) idle

namespace Controls

/-- The rule that takes `(p x)` and makes `(q x)`. -/
def pToQ : MadeRule :=
  ⟨[(Mode.take, .expression [.symbol "p", .var "x"])], [], .expression [.symbol "q", .var "x"]⟩

/-- On a store with no `(p _)` the rule is idle. -/
theorem pToQ_idle : Idle [pToQ] [b, .expression [.symbol "q", a]] := by
  intro r member
  simp only [List.mem_singleton] at member
  subst member
  decide

/-- On a store with `(p a)` it is not: its one branch fires. -/
theorem pToQ_not_idle : ¬ Idle [pToQ] [.expression [.symbol "p", a], b] := by
  intro idle
  have none := idle pToQ (List.mem_singleton_self _)
  revert none
  decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
