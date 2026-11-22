import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Correspondence

/-!
# Every source step is one firing, and every firing is a source step

For programs of the first fragment (`ret`, `apply`, `choice`, `fail`, equations under binders with
second-order patterns in their left sides):

* **`simulation`**: a source step of a represented alternative makes a bag of alternatives; for each
  live one there is exactly one firing to a state that represents it.
* **`reflection`**: every admitted firing from a state that represents an alternative is a source
  step of that alternative, and its result represents one of the alternatives that step makes.

The unmatched call: admission of the fixed rule `unmatchedRule` (`absent eqn(T)`) holds exactly when
no equation of the program matches the call (`unmatched_guard` for the source's condition implying
the check; `unmatched_none` for the converse).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## Membership of the rules -/

section Members

variable {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)

theorem retRule_mem : retRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inl rfl)))
theorem unmatchedRule_mem : unmatchedRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inr (.inl rfl))))
theorem choiceLeftRule_mem : choiceLeftRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inr (.inr (.inl rfl)))))
theorem choiceRightRule_mem : choiceRightRule N ∈ translate N P :=
  (mem_translate N).mpr (.inl ((mem_controlRules N).mpr (.inr (.inr (.inr (.inl rfl))))))
theorem schema_mem {e : SourceLanguage.Equation κ Γ star Ty} (member : e ∈ P.equations) :
    schema N e ∈ translate N P :=
  (mem_translate N).mpr (.inr ⟨e, member, rfl⟩)

end Members

/-! ## Shapes read back from one reading -/

section Shapes

variable {Ty : Type} {b : Branch κ Γ star Ty} {B : Interface.Frames.Frame S}

theorem focus_eval_of_reads {x y : Term (signature S B.arity) Γ star}
    (reads : branchReads N b B (observe (altN N (evalN N x) y))) :
    ∃ (σ : Assignment (fam κ) B.arity) (c : Comp κ Γ star Ty), Models σ b.store ∧ b.focus = .eval c ∧
      x = encComp N (instantiate σ) c ∧ y = encStack N (instantiate σ) b.frames := by
  obtain ⟨σ, solved, same⟩ := (branchReads_observe N).mp reads
  obtain ⟨onFocus, onStack⟩ := alt_eq_encAlt N (instantiate σ) same.symm
  obtain ⟨c, focus, onComp⟩ := eval_eq_encFocus N (instantiate σ) onFocus
  exact ⟨σ, c, solved, focus, onComp, onStack⟩

theorem shape_ret {h : Assignment (unknownArity Γ star) B.arity}
    (reads : branchReads N b B (instantiateObservation h
      (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))))) :
    ∃ t, b.focus = .eval (.ret t) := by
  change branchReads N b B (observe (instantiate h _)) at reads
  rw [instantiate_altN, instantiate_evalN, instantiate_retN] at reads
  obtain ⟨σ, c, _, focus, onComp, _⟩ := focus_eval_of_reads N reads
  obtain ⟨t, rfl, _⟩ := ret_eq_encComp N (instantiate σ) onComp
  exact ⟨t, focus⟩

theorem shape_apply {x : Term (signature S B.arity) Γ star} {y : Term (signature S B.arity) Γ star}
    (reads : branchReads N b B (observe (altN N (evalN N (applyN N x)) y))) :
    ∃ (t : Data κ Γ star) (σ : Assignment (fam κ) B.arity), b.focus = .eval (.apply t) ∧
      Models σ b.store ∧ instantiate σ t = x := by
  obtain ⟨σ, c, solved, focus, onComp, _⟩ := focus_eval_of_reads N reads
  obtain ⟨t, rfl, onCall⟩ := apply_eq_encComp N (instantiate σ) onComp
  exact ⟨t, σ, focus, solved, onCall.symm⟩

theorem shape_choice {h : Assignment (unknownArity Γ star) B.arity}
    (reads : branchReads N b B (instantiateObservation h
      (observe (altN N (evalN N (choiceN N (unk .first) (unk .second))) (unk .stack))))) :
    ∃ c d, b.focus = .eval (.choice c d) := by
  change branchReads N b B (observe (instantiate h _)) at reads
  rw [instantiate_altN, instantiate_evalN, instantiate_choiceN] at reads
  obtain ⟨σ, c, _, focus, onComp, _⟩ := focus_eval_of_reads N reads
  obtain ⟨c₁, c₂, rfl, _⟩ := choice_eq_encComp N (instantiate σ) onComp
  exact ⟨c₁, c₂, focus⟩

theorem shape_bindStart {h : Assignment (unknownArity Γ star) B.arity}
    (reads : branchReads N b B (instantiateObservation h
      (observe (altN N (evalN N (bindN N (unk .pattern) (unk .first) (unk .second))) (unk .stack))))) :
    ∃ s p c k, b.focus = .eval (.let_ s p c k) := by
  change branchReads N b B (observe (instantiate h _)) at reads
  rw [instantiate_altN, instantiate_evalN, instantiate_bindN] at reads
  obtain ⟨σ, c, _, focus, onComp, _⟩ := focus_eval_of_reads N reads
  obtain ⟨s, p, c₁, k, rfl, _⟩ := bind_eq_encComp N (instantiate σ) onComp
  exact ⟨s, p, c₁, k, focus⟩

theorem shape_bindValue {h : Assignment (unknownArity Γ star) B.arity}
    (reads : branchReads N b B (instantiateObservation h
      (observe (altN N (valueN N (unk .datum)) (pushN N (unk .pattern) (unk .second) (unk .stack)))))) :
    ∃ s p k fs, b.frames = .bindTo s p k :: fs := by
  change branchReads N b B (observe (instantiate h _)) at reads
  rw [instantiate_altN, instantiate_valueN, instantiate_pushN] at reads
  obtain ⟨σ, _, same⟩ := (branchReads_observe N).mp reads
  obtain ⟨_, onStack⟩ := alt_eq_encAlt N (instantiate σ) same.symm
  obtain ⟨s, p, k, fs, frames, _⟩ := push_eq_encStack N (instantiate σ) onStack
  exact ⟨s, p, k, fs, frames⟩

end Shapes

/-! ## Freshness of the next alternative -/

section NextFresh

variable {Ty : Type}

theorem branchBelow_focus {n : ℕ} {b b' : Branch κ Γ star Ty} (below : BranchBelow n b)
    (store : b'.store = b.store) (frames : b'.frames = b.frames)
    (focus : ∀ t ∈ focusData b'.focus, t ∈ focusData b.focus) : BranchBelow n b' :=
  ⟨by rw [store]; exact below.1, fun t member => below.2.1 t (focus t member),
    by rw [frames]; exact below.2.2⟩

theorem branchBelow_call {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    (below : BranchBelow n ⟨K, .eval (.apply t), fs, ps⟩) (e : SourceLanguage.Equation κ Γ star Ty) :
    BranchBelow (n + 1)
      ⟨K ++ [(instantiate (copyAt κ n) e.lhs, t)], .eval (e.rhs.inst (copyAt κ n)), fs, ps⟩ := by
  have callBelow : DependsBelow n t := below.2.1 t (by simp [focusData, Comp.data])
  refine ⟨?_, ?_, ?_⟩
  · intro e' member
    rcases List.mem_append.mp member with old | new
    · exact ⟨DependsBelow.mono (below.1 e' old).1 (Nat.le_succ n),
        DependsBelow.mono (below.1 e' old).2 (Nat.le_succ n)⟩
    · rw [List.mem_singleton.mp new]
      exact ⟨dependsBelow_copy n e.lhs, DependsBelow.mono callBelow (Nat.le_succ n)⟩
  · intro t' member
    change t' ∈ (e.rhs.mapData (instantiate (copyAt κ n))).data at member
    rw [comp_data_mapData] at member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact dependsBelow_copy n original
  · intro fr member t' inside
    exact DependsBelow.mono (below.2.2 fr member t' inside) (Nat.le_succ n)

end NextFresh

/-! ## The unmatched call -/

section Unmatched

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- The term the absence check of `unmatchedRule` reads. -/
abbrev unmatchedCheck : Observation S (unknownArity Γ star) := observe (eqnN N (unk .datum))

/-- **No equation matches, so the check holds**: when no equation of the program matches the call,
the absence check of the canonical unmatched firing holds at every solution of its information. -/
theorem unmatched_guard {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {s : HostState S} {a : ℕ} (rep : Represents N P n ⟨K, .eval (.apply t), fs, ps⟩ s a)
    (none : ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)])) :
    (Interface.Frames.contextual S).Entails
      ((canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).information (Interface.Frames.contextual S) s)
      (fun _ σ => (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).Holds
        (Interface.Frames.contextual S) s σ) := by
  have simple := canonical_simple (s := s) (r := unmatchedRule N) (member := unmatchedRule_mem N P) (a := a)
    (pat := observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
    (out := observe (altN N (valueN N (unk .datum)) (unk .stack))) rfl rfl rfl
  intro B u solved
  obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
  refine ⟨?_, ?_⟩
  · intro c member
    change c ∈ [Check.predicate .none (instantiateObservation
      (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).opening (unmatchedCheck N))] at member
    rw [List.mem_singleton] at member
    subst member
    intro o present equal
    change instantiateObservation u (instantiateObservation _ (unmatchedCheck N)) =
      instantiateObservation u (instantiateObservation _ (s.label o)) at equal
    rw [instantiateObservation_comp, instantiateObservation_comp] at equal
    -- the alternative's reading
    have readsAlt : rowReads s a B (instantiateObservation (Assignment.compose u
        (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).opening)
        (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))) := ⟨_, known, matched.symm⟩
    have readsB := (rep.reads B _).mp readsAlt
    change branchReads N _ B (observe (instantiate _ _)) at readsB
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at readsB
    obtain ⟨t', σ, focus, solvedσ, onCall⟩ := shape_apply N readsB
    simp only [Focus.eval.injEq, Comp.apply.injEq] at focus
    subst focus
    have equal' : observe (eqnN N (instantiate σ t)) = instantiateObservation (Assignment.compose u
        ((RuleSyntax.Contextual.declarations S).weaken
          (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).ext)) (s.label o) := by
      rw [onCall, ← instantiate_eqnN]
      exact equal
    rw [rep.present, Finset.mem_insert, Finset.mem_range] at present
    rcases present with rfl | small
    · -- the alternative's own row is not an equation row
      have row : instantiateObservation (Assignment.compose u
          (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) o).opening)
          (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) =
          observe (eqnN N (instantiate σ t)) := matched.trans equal'.symm
      change observe (instantiate _ (altN N _ _)) = _ at row
      rw [instantiate_altN] at row
      exact absurd (N.tag_eq (observe_injective row)) (by decide)
    · obtain ⟨θ, row⟩ := rep.rows B _ known o small
      have sameCall := vec1_inj (N.args_eq (observe_injective (equal'.trans row)))
      apply none _ (List.get_mem P.equations ⟨o, small⟩)
      exact (solvable_copy_iff _ rep.fresh.1 (rep.fresh.2.1 t (by simp [focusData, Comp.data]))).mpr
        ⟨_, _, σ, θ, solvedσ, sameCall.symm⟩
  · intro q member
    have empty : (canonicalAt s (unmatchedRule N) (unmatchedRule_mem N P) a).collectOpened
        (Interface.Frames.contextual S) = [] := rfl
    rw [empty] at member
    simp at member

/-- **The check holds, so no equation matches**: if an unmatched firing taking the alternative's row
is admitted, no equation of the program matches the call. -/
theorem unmatched_none {n : ℕ} {K : List (Constraint κ Γ star)} {t : Data κ Γ star}
    {fs : List (SourceLanguage.Frame κ Γ star Ty)} {ps : List (Data κ Γ star × Comp κ Γ star Ty)}
    {s : HostState S} {a a' : ℕ} (rep : Represents N P n ⟨K, .eval (.apply t), fs, ps⟩ s a)
    {member : unmatchedRule N ∈ translate N P} {ext : (RuleSyntax.Contextual.declarations S).Ext s.frame}
    {opening : Assignment (unmatchedRule N).locals.arity
      ((RuleSyntax.Contextual.declarations S).target ext).arity}
    {selection : Selection ℕ} {seen : List (Finset ℕ)}
    (simple : Simple (⟨unmatchedRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame) a a'
      (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack)))
      (observe (altN N (valueN N (unk .datum)) (unk .stack))))
    (admitted : RuleSyntax.Firing.Admits (Interface.Frames.contextual S) s
      (⟨unmatchedRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)) :
    ∀ e ∈ P.equations, ¬ Solvable (K ++ [(instantiate (copyAt κ n) e.lhs, t)]) := by
  intro e member' solvable
  obtain ⟨i, rfl⟩ := List.get_of_mem member'
  obtain ⟨W, target, σ, θ, solvedσ, matchedθ⟩ :=
    (solvable_copy_iff _ rep.fresh.1 (rep.fresh.2.1 t (by simp [focusData, Comp.data]))).mp solvable
  let B : Interface.Frames.Frame S := ⟨W, target⟩
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have readsB : branchReads N (⟨K, .eval (.apply t), fs, ps⟩ : Branch κ Γ star Ty) B
      (observe (encBranch N (instantiate σ) (⟨K, .eval (.apply t), fs, ps⟩ : Branch κ Γ star Ty))) :=
    ⟨σ, solvedσ, rfl⟩
  obtain ⟨g, known, readG⟩ := (rep.reads B _).mpr readsB
  obtain ⟨g', known', sameAlt, rowI⟩ := rep.independent B g known i.1 i.2 θ
  let h : Assignment (unknownArity Γ star) B.arity :=
    fill (instantiate σ t) (instantiate σ t) (instantiate σ t) (instantiate σ t)
      (encStack N (instantiate σ) fs)
  have matchedH : instantiateObservation h (observe (altN N (evalN N (applyN N (unk .datum))) (unk .stack))) =
      instantiateObservation g' (s.label a) := by
    rw [sameAlt, readG]
    change observe (instantiate h _) = _
    rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_unk, instantiate_unk]
    rfl
  obtain ⟨u, solvedU, _, onRows, onTerms⟩ :=
    simple_amalgamate simple admitted.1.1 aPresent g' h known' (fun _ inside => by cases inside) matchedH
  have holds := (admitted.2.2.2 B u solvedU).1
  have checkMember : (RuleSyntax.Firing.opened (Interface.Frames.contextual S)
      (⟨unmatchedRule N, member, ext, opening, selection, seen⟩ :
        RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)).checks =
      [.predicate .none (instantiateObservation opening (unmatchedCheck N))] := rfl
  have absent := holds _ (by rw [checkMember]; exact List.mem_singleton_self _)
  have iPresent : i.1 ∈ s.present := by
    rw [rep.present]; exact Finset.mem_insert_of_mem (Finset.mem_range.mpr i.2)
  apply absent i.1 iPresent
  change instantiateObservation u (instantiateObservation opening (unmatchedCheck N)) =
    instantiateObservation u (RuleSyntax.Firing.row (Interface.Frames.contextual S) s _ i.1)
  rw [onTerms _ (by simp [RuleSyntax.Rule.terms, unmatchedRule, RuleSyntax.checkTerms]),
    onRows i.1 iPresent, rowI]
  change observe (instantiate h (eqnN N (unk .datum))) = _
  rw [instantiate_eqnN, instantiate_unk]
  change observe (eqnN N (instantiate σ t)) = observe (eqnN N (instantiate θ (P.equations.get i).lhs))
  rw [matchedθ]

end Unmatched

#print axioms shape_ret
#print axioms branchBelow_call
#print axioms unmatched_guard
#print axioms unmatched_none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
