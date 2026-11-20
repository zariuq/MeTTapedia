import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Isolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingFirstOrder

/-!
# Privacy at the start suffices: success persists for every positive run

`Composition.success_persists` asks every step of the run to be private from the neighbour, the
firing's own fresh unknowns included. At first-order terms over infinitely many unknowns, privacy
at the start is enough: the run's fresh unknowns are finitely many, so the neighbour's unknowns can
be renamed away from them, and renaming is a bisimulation.

* `exists_perm_moving`: over infinitely many unknowns, a permutation fixes a finite set and moves a
  finite set disjoint from it outside any third finite set.
* `stateUnknowns`, `footprintUnknowns`: the unknowns a state, and a firing's footprint, mention form
  finite sets; `run_within`: every positive run has all its footprints inside one finite set.
* `renameState_congruent_of_fixed`, `congruent_beside_right`, `reaches_of_congruent`: renaming that
  fixes a state's terms gives a congruent state; congruence passes to compositions and preserves
  reachable success.
* **`success_persists_from_start`**: if the system reaches success by positive firings whose made
  identities avoid the neighbour's rows, the neighbour is solvable and shares no unknown with the
  system's start, and the barb is invariant under renaming, then the composition reaches success.

Control (`success_despite_opened_collision`): beside a neighbour that mentions the very unknown the
request's run opens (so that run is not private, `CompositionControls.opened_not_fresh`), success
still persists, because only the start must be private. The shared-unknown control
(`CompositionControls.shared_success_unreachable`) shows that privacy at the start is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Mettapedia.Logic.LP

universe uV uO

/-! ## Permutations that move a finite set away -/

section Permutations

variable {V : Type uV} [DecidableEq V] [Infinite V]

/-- **A permutation fixes a finite set and moves a finite set disjoint from it outside any third
finite set.** -/
theorem exists_perm_moving (Dv : Finset V) :
    ∀ (K U : Finset V), Disjoint K Dv → ∃ e : V ≃ V, (∀ v ∈ K, e v = v) ∧ ∀ d ∈ Dv, e d ∉ U := by
  induction Dv using Finset.induction_on with
  | empty =>
      intro K U _
      exact ⟨Equiv.refl V, fun _ _ => rfl, fun d member => absurd member (Finset.notMem_empty d)⟩
  | insert d Dv' notIn ih =>
      intro K U disjoint
      obtain ⟨dK, disjointK⟩ := Finset.disjoint_insert_right.mp disjoint
      obtain ⟨e₀, fixes₀, moves₀⟩ := ih (insert d K) U
        (Finset.disjoint_insert_left.mpr ⟨notIn, disjointK⟩)
      obtain ⟨x, fresh⟩ := Infinite.exists_notMem_finset (U ∪ insert d K ∪ Dv'.image e₀)
      have xU : x ∉ U := fun inside => fresh (by simp [inside])
      have xK : x ∉ insert d K := fun inside => fresh (by simp only [Finset.mem_union]; tauto)
      have xImage : x ∉ Dv'.image e₀ := fun inside => fresh (by simp only [Finset.mem_union]; tauto)
      have dFixed : e₀ d = d := fixes₀ d (Finset.mem_insert_self d K)
      refine ⟨e₀.trans (Equiv.swap d x), fun v member => ?_, fun d' member => ?_⟩
      · have fixed : e₀ v = v := fixes₀ v (Finset.mem_insert_of_mem member)
        rw [Equiv.trans_apply, fixed]
        have notD : v ≠ d := fun same => dK (same ▸ member)
        have notX : v ≠ x := fun same => xK (same ▸ Finset.mem_insert_of_mem member)
        exact Equiv.swap_apply_of_ne_of_ne notD notX
      · rw [Equiv.trans_apply]
        rcases Finset.mem_insert.mp member with rfl | inRest
        · rw [dFixed, Equiv.swap_apply_left]
          exact xU
        · have notDImage : e₀ d' ≠ d := fun same => notIn (e₀.injective (same.trans dFixed.symm) ▸ inRest)
          have notXImage : e₀ d' ≠ x := fun same => xImage (Finset.mem_image.mpr ⟨d', inRest, same⟩)
          rw [Equiv.swap_apply_of_ne_of_ne notDImage notXImage]
          exact moves₀ d' inRest

end Permutations

/-! ## Congruence: renaming that fixes a state, compositions, reachable success -/

section Congruence

universe uT uS

variable {T : Type uT} {S : Type uS} {A : SubstitutionAction T S} {O : Type uO} [DecidableEq O]

omit [DecidableEq O] in
/-- **A renaming that fixes every term a state mentions gives a congruent state.** -/
theorem renameState_congruent_of_fixed (π : Renaming A) {s : State (Terms T) O}
    (fixed : ∀ t, s.Mentions t → A.apply π.forward t = t) : Congruent (renameState π s) s := by
  have store : renameStore π s.knowledge = s.knowledge := by
    unfold renameStore
    conv_rhs => rw [← List.map_id s.knowledge]
    apply List.map_congr_left
    intro e member
    show (A.apply π.forward e.1, A.apply π.forward e.2) = e
    rw [fixed e.1 (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)),
      fixed e.2 (Or.inr (Or.inl (List.mem_map.mpr ⟨e, member, rfl⟩)))]
  refine ⟨fun e => ?_, rfl, fun o present => fixed _ (Or.inr (Or.inr ⟨o, present, rfl⟩))⟩
  show e ∈ renameStore π s.knowledge ↔ e ∈ s.knowledge
  rw [store]

/-- **Congruence passes to compositions.** -/
theorem congruent_beside_right {D C C' : State (Terms T) O} (apart : Disjoint D.present C.present)
    (same : Congruent C C') : Congruent (beside D C) (beside D C') := by
  have apart' : Disjoint D.present C'.present := same.present ▸ apart
  refine ⟨fun e => ?_, ?_, fun o present => ?_⟩
  · show e ∈ D.knowledge ++ C.knowledge ↔ e ∈ D.knowledge ++ C'.knowledge
    rw [List.mem_append, List.mem_append, same.knowledge e]
  · show D.present ∪ C.present = D.present ∪ C'.present
    rw [same.present]
  · rcases Finset.mem_union.mp present with inD | inC
    · rw [beside_label_left inD, beside_label_left inD]
    · rw [beside_label_right apart inC, beside_label_right apart' (same.present ▸ inC)]
      exact same.label o inC

/-- Runs lift along congruence. -/
theorem run_congruent {P : Program (Terms T)} {s t s' : State (Terms T) O} (same : Congruent s t)
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s') :
    ∃ t', Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) t t' ∧ Congruent s' t' := by
  induction run with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, same⟩
  | tail _ last ih =>
      obtain ⟨t₁, run₁, related⟩ := ih
      obtain ⟨t₂, step₂, related₂⟩ := succ_congruent related last
      exact ⟨t₂, run₁.tail step₂, related₂⟩

/-- **Reachable success is invariant under congruence.** -/
theorem reaches_of_congruent {P : Program (Terms T)} {barb : T → Prop} {s t : State (Terms T) O}
    (same : Congruent s t)
    (reaches : ∃ s', Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s' ∧
      Succeeds barb s') :
    ∃ t', Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) t t' ∧ Succeeds barb t' := by
  obtain ⟨s', run, ⟨o, present, holds⟩⟩ := reaches
  obtain ⟨t', run', related⟩ := run_congruent same run
  exact ⟨t', run', o, related.present ▸ present, by rw [← related.label o present]; exact holds⟩

end Congruence

/-! ## The unknowns of a run are finitely many -/

/-- A run of one relation is a run of any larger relation. -/
theorem reflTransGen_imp {α : Type uV} {r p : α → α → Prop} (larger : ∀ a b, r a b → p a b) {a b : α}
    (run : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ last ih => exact ih.tail (larger _ _ last)

section Runs

variable {sig : LPSignature} [DecidableEq sig.vars] {O : Type uO} [DecidableEq O]

local notation "FO" => FirstOrder.action sig

/-- The unknowns of a list of terms. -/
def termsUnknowns : List (Term sig) → Finset sig.vars
  | [] => ∅
  | t :: ts => t.freeVars ∪ termsUnknowns ts

omit [DecidableEq O] in
theorem mem_termsUnknowns {ts : List (Term sig)} {v : sig.vars} :
    v ∈ termsUnknowns ts ↔ ∃ t ∈ ts, v ∈ t.freeVars := by
  induction ts with
  | nil => simp [termsUnknowns]
  | cons t ts ih =>
      simp only [termsUnknowns, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (inside | ⟨u, member, inside⟩)
        · exact ⟨t, Or.inl rfl, inside⟩
        · exact ⟨u, Or.inr member, inside⟩
      · rintro ⟨u, rfl | member, inside⟩
        · exact Or.inl inside
        · exact Or.inr ⟨u, member, inside⟩

/-- **The unknowns a state mentions, as a finite set.** -/
def stateUnknowns (s : State (Terms (Term sig)) O) : Finset sig.vars :=
  eqVars s.knowledge ∪ s.present.biUnion fun o => (s.label o).freeVars

omit [DecidableEq O] in
theorem unknowns_iff_stateUnknowns (s : State (Terms (Term sig)) O) (v : sig.vars) :
    UnknownsOf s.Mentions v ↔ v ∈ stateUnknowns s := by
  rw [unknowns_mentions, unknowns_storeTerms_iff]
  unfold stateUnknowns
  rw [Finset.mem_union, Finset.mem_biUnion]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨t, ⟨o, present, rfl⟩, inside⟩
    exact ⟨o, present, inside⟩
  · rintro ⟨o, present, inside⟩
    exact ⟨_, ⟨o, present, rfl⟩, inside⟩

/-- The unknowns of a firing's footprint, as a finite set. -/
def footprintUnknowns {P : Program (Terms (Term sig))} (s : State (Terms (Term sig)) O)
    (f : Firing O (ext FO) P PUnit.unit) : Finset sig.vars :=
  stateUnknowns s ∪ termsUnknowns (f.rule.terms.map (Subst.applyTerm f.opening))

omit [DecidableEq O] in
theorem footprint_mem_unknowns {P : Program (Terms (Term sig))} {s : State (Terms (Term sig)) O}
    {f : Firing O (ext FO) P PUnit.unit} {v : sig.vars} (inside : UnknownsOf (Footprint FO s f) v) :
    v ∈ footprintUnknowns s f := by
  obtain ⟨t, foot, member⟩ := inside
  unfold footprintUnknowns
  rw [Finset.mem_union]
  rcases foot with mentioned | opened
  · exact Or.inl ((unknowns_iff_stateUnknowns s v).mp ⟨t, mentioned, member⟩)
  · exact Or.inr (mem_termsUnknowns.mpr ⟨t, opened, member⟩)

variable (P : Program (Terms (Term sig)))

/-- **A positive step** of the program, whose made identities avoid the identities `I`. -/
def PositiveStep (I : Finset O) (C C' : State (Terms (Term sig)) O) : Prop :=
  ∃ f : Firing O (ext FO) P PUnit.unit, (step (frames FO) O (ext FO) P).Admits (s := C) f ∧
    Positive f.rule ∧ (∀ o ∈ f.selection.made, o ∉ I) ∧ f.result (frames FO) C = C'

/-- A positive step whose footprint mentions only unknowns of `U`. -/
def StepWithin (I : Finset O) (U : Finset sig.vars) (C C' : State (Terms (Term sig)) O) : Prop :=
  ∃ f : Firing O (ext FO) P PUnit.unit, (step (frames FO) O (ext FO) P).Admits (s := C) f ∧
    Positive f.rule ∧ (∀ o ∈ f.selection.made, o ∉ I) ∧
      (∀ v, UnknownsOf (Footprint FO C f) v → v ∈ U) ∧ f.result (frames FO) C = C'

variable {P}

/-- **Every positive run has all its footprints inside one finite set of unknowns.** -/
theorem run_within {I : Finset O} {C C' : State (Terms (Term sig)) O}
    (run : Relation.ReflTransGen (PositiveStep P I) C C') :
    ∃ U, Relation.ReflTransGen (StepWithin P I U) C C' := by
  induction run with
  | refl => exact ⟨∅, Relation.ReflTransGen.refl⟩
  | @tail b c _ last ih =>
      obtain ⟨U, within⟩ := ih
      obtain ⟨f, admitted, positive, avoid, rfl⟩ := last
      refine ⟨U ∪ footprintUnknowns b f, Relation.ReflTransGen.tail (b := b) ?_ ?_⟩
      · exact reflTransGen_imp (fun _ _ ⟨g, admitted', positive', avoid', inU, result⟩ =>
          ⟨g, admitted', positive', avoid', fun v foot => Finset.mem_union_left _ (inU v foot), result⟩)
          within
      · exact ⟨f, admitted, positive, avoid,
          fun v foot => Finset.mem_union_right _ (footprint_mem_unknowns foot), rfl⟩

/-! ## Privacy at the start suffices -/

/-- **Success persists for every positive run when the neighbour shares no unknown with the start.**
The run's made identities avoid the neighbour's rows, the neighbour is solvable, and the barb is
invariant under renaming. -/
theorem success_persists_from_start [Infinite sig.vars] {barb : Term sig → Prop}
    (invariant : ∀ e : sig.vars ≃ sig.vars, ∀ t, barb (Subst.applyTerm (permSubst e) t) ↔ barb t)
    {D C C' : State (Terms (Term sig)) O}
    (run : Relation.ReflTransGen (PositiveStep P D.present) C C') (succeeds : Succeeds barb C')
    (apart : Disjoint D.present C.present) (solvableD : (FirstOrder.action sig).Consistent D.knowledge)
    (privateStart : ∀ v, UnknownsOf D.Mentions v → ¬ UnknownsOf C.Mentions v) :
    ∃ t, Relation.ReflTransGen (Succ (step (frames FO) O (ext FO) P).toStep) (beside D C) t ∧
      Succeeds barb t := by
  obtain ⟨U, within⟩ := run_within run
  have disjointCD : Disjoint (stateUnknowns C) (stateUnknowns D) := by
    rw [Finset.disjoint_left]
    intro v inC inD
    exact privateStart v ((unknowns_iff_stateUnknowns D v).mpr inD)
      ((unknowns_iff_stateUnknowns C v).mpr inC)
  obtain ⟨e, fixes, moves⟩ := exists_perm_moving (stateUnknowns D) (stateUnknowns C) U disjointCD
  let π : Renaming FO := permutation e
  have avoid : ∀ v, UnknownsOf (renameState π D).Mentions v → v ∉ U := by
    rintro v ⟨t, mentioned, inside⟩
    obtain ⟨t₀, mentioned₀, rfl⟩ := (mentions_rename π D).mp mentioned
    obtain ⟨w, inT₀, inW⟩ := Subst.mem_freeVars_applyTerm.mp inside
    have isE : v = e w := Term.mem_freeVars_var.mp inW
    subst isE
    exact moves w ((unknowns_iff_stateUnknowns D w).mp ⟨t₀, mentioned₀, inT₀⟩)
  have privateRun : Relation.ReflTransGen (PrivateStep FO P (renameState π D)) C C' :=
    reflTransGen_imp (fun _ _ ⟨f, admitted, positive, madeNew, inU, result⟩ =>
      ⟨f, admitted, positive, independent_of_disjoint fun v inD inFoot => avoid v inD (inU v inFoot),
        madeNew, result⟩) within
  have solvableD' : (FirstOrder.action sig).Consistent (renameState π D).knowledge := by
    obtain ⟨σ, solved⟩ := solvableD
    exact ⟨(FirstOrder.action sig).compose σ π.backward,
      (models_renameStore π _ _).mpr ((models_congr_apply (apply_undo π σ) _).mpr solved)⟩
  obtain ⟨t, reached, holds⟩ := success_persists privateRun succeeds apart solvableD'
  have fixedC : ∀ t, C.Mentions t → (FirstOrder.action sig).apply π.forward t = t := by
    intro t mentioned
    apply Subst.applyTerm_eq_self
    intro v inside
    show Term.var (e v) = Term.var v
    rw [fixes v ((unknowns_iff_stateUnknowns C v).mp ⟨t, mentioned, inside⟩)]
  have related : Congruent (beside (renameState π D) C) (renameState π (beside D C)) := by
    rw [renameState_beside]
    exact congruent_beside_right apart (renameState_congruent_of_fixed π fixedC).symm
  exact (reaches_rename_iff π (invariant e) (beside D C)).mp
    (reaches_of_congruent related ⟨t, reached, holds⟩)

end Runs

/-! ## Control: the run's own unknown may collide with the neighbour -/

namespace StartPrivacyControls

open Examples (Tm X E x c)
open CompositionControls
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

theorem nine_invariant (e : ℕ ≃ ℕ) (t : Term atoms) :
    Subst.applyTerm (permSubst (sig := atoms) e) t = c 9 ↔ t = c 9 := by
  constructor
  · intro renamed
    have back : Subst.applyTerm (permSubst (sig := atoms) e.symm)
        (Subst.applyTerm (permSubst (sig := atoms) e) t) = t := permSubst_cancel e t
    rw [renamed] at back
    exact back.symm
  · rintro rfl
    rfl

/-- **Success persists beside a neighbour that mentions the request's opened unknown**: the
request's own run is not private from it (`CompositionControls.opened_not_fresh`), yet only the
start must be private. -/
theorem success_despite_opened_collision :
    ¬ tellAt.Fresh X (beside mentionsOpened request) ∧
      ∃ t, Relation.ReflTransGen (Succ (step X ℕ E tellProgram).toStep) (beside mentionsOpened request) t ∧
        Succeeds (· = c 9) t := by
  refine ⟨opened_not_fresh, ?_⟩
  refine success_persists_from_start (sig := atoms) nine_invariant
    (.single ⟨tellAt, tellAt_admitted, tellRule_positive, by simp [mentionsOpened, tellAt], rfl⟩)
    result_succeeds (Finset.disjoint_empty_left _) ⟨fun _ => c 0, fun e member => by
      simp only [mentionsOpened, List.mem_singleton] at member
      subst member
      rfl⟩ ?_
  intro v inD inC
  have one := mentionsOpened_unknowns inD
  obtain ⟨t, mentioned, member⟩ := inC
  rw [request_mentions mentioned] at member
  have zero := freeVars_var 0 member
  omega

end StartPrivacyControls

#print axioms exists_perm_moving
#print axioms renameState_congruent_of_fixed
#print axioms congruent_beside_right
#print axioms reaches_of_congruent
#print axioms run_within
#print axioms success_persists_from_start
#print axioms StartPrivacyControls.success_despite_opened_collision

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope
