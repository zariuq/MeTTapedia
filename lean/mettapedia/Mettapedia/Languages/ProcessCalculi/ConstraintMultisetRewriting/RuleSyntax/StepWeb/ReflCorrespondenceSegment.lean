import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceReflect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceExample

/-!
# The reflection of the child's segment applies

`refl_reflects` speaks about every commit, cooling run and close from a heated child. Here a heated child of the
manuscript's reflected redex: the reflection, the child's token and the two represented inputs at the child.

* `segment_runs`: a commit, a cooling run after it and a close at its end exist there (so `refl_reflects` is not
  about an empty set of runs);
* `segment_reflects`: `refl_reflects` applies to every such run: the commit is the source's COMM on the child's bag
  and the made row reads as the listener of `[predot (applyDot bs 0), predot (applyDot bs y)]`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar tProc pReflect applyDot demoChan)
open MeTTaOperationsComm (psubst PSubst pvars)
open FiniteProgram (predot)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE nameLaws_of_eq nameLaws_heads)
open ReflLocated (atLoc rootLoc childLoc pendingTok doneTok located locatedFrame_name psubst_rootLoc psubst_atLoc_any)
open ReflPacking (CoolRun psubst_doneTok)
open ReflLocatedStep (psubst_childLoc solution_of_admitted res resConf commChildAt)
open Comm.Controls (zeroTerm y unifier unifier_groundPrincipal)
open FiniteProgram.Controls (example_apart unifier_values)
open ReflQuotient.Controls (yToZero)

/-- The child of the example's reflection. -/
def exampleChild : Pattern := childLoc rootLoc demoChan exampleProcess

/-- A heated child: the reflection at `0`, the child's token at `1`, its two represented inputs at `2` and `3`. -/
def segRows : ℕ → Pattern := fun o =>
  if o = 0 then atLoc (pReflect demoChan exampleProcess) rootLoc
  else if o = 1 then pendingTok exampleChild rootLoc
  else if o = 2 then atLoc (predot (pFor zeroTerm demoChan pZero)) exampleChild
  else atLoc (predot (pFor y demoChan y)) exampleChild

def segConf : Configuration Pattern ℕ := ⟨[], {0, 1, 2, 3}⟩

theorem segRows_zero : segRows 0 = atLoc (pReflect demoChan exampleProcess) rootLoc := rfl
theorem segRows_one : segRows 1 = pendingTok exampleChild rootLoc := rfl
theorem segRows_two : segRows 2 = atLoc (predot (pFor zeroTerm demoChan pZero)) exampleChild := rfl
theorem segRows_three : segRows 3 = atLoc (predot (pFor y demoChan y)) exampleChild := rfl

/-- The root row is not at the child, at any solution. -/
theorem segRoot_not_child (σ : PSubst) (z : Pattern) :
    ¬ NameLaws (psubst σ (segRows 0)) (atLoc z (psubst σ exampleChild)) := by
  intro same
  rw [segRows_zero, psubst_atLoc_any, psubst_rootLoc, exampleChild, psubst_childLoc, psubst_rootLoc] at same
  exact absurd (nameLaws_heads ((locatedFrame_name.atLoc_iff _ _ _ _).mp same).2) (by decide)

/-- **Runs of the segment exist**: from the heated child, a commit, a cooling run after it and a close at its end. -/
theorem segment_runs :
    ∃ (ρ : PSubst) (label₄ : ℕ → Pattern) (C₄ : Configuration Pattern ℕ) (d' : ℕ) (rows : List Pattern) (ρ₅ : PSubst),
      (RuleSyntax.step QN ℕ QNE located).Admits (s := embed segRows segConf) (commChildAt ρ 2 3 1 4 5 6) ∧
      CoolRun exampleChild rootLoc (res segRows segConf (commChildAt ρ 2 3 1 4 5 6)).label
        (resConf segRows segConf (commChildAt ρ 2 3 1 4 5 6)) 6 label₄ C₄ d' rows ∧
      (RuleSyntax.step QN ℕ QNE located).Admits (s := embed label₄ C₄) (closeRootAt ρ₅ 0 d' 7) := by
  obtain ⟨ρ, fresh⟩ := commit_fresh_exists segRows segConf 2 3 1 4 5 6
  obtain ⟨committed, reads⟩ := child_commit segRows segConf zeroTerm y demoChan pZero y exampleChild rootLoc unifier
    unifier_groundPrincipal example_apart (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2 3 1 4 5 6
    (fun σ _ => by rw [segRows_two]; exact ReflNames.NameLaws.refl _)
    (fun σ _ => by rw [segRows_three]; exact ReflNames.NameLaws.refl _)
    (fun σ _ => by rw [segRows_one]; exact ReflNames.NameLaws.refl _)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) (σ₀ := yToZero)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel) fresh
  have present₃ : ∀ o, o ∈ (resConf segRows segConf (commChildAt ρ 2 3 1 4 5 6)).present ↔
      (o ∈ segConf.present ∧ o ≠ 2 ∧ o ≠ 3 ∧ o ≠ 1) ∨ o = 4 ∨ o = 5 ∨ o = 6 :=
    fun o => commit_present segRows segConf ρ 2 3 1 4 5 6 o
  have inSeg : ∀ o, o ∈ segConf.present ↔ o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by
    intro o
    simp [segConf]
  obtain ⟨label₄, C₄, d', ρ₅, coolRun, closed, -, -⟩ := refl_commit_closes
    (res segRows segConf (commChildAt ρ 2 3 1 4 5 6)).label (resConf segRows segConf (commChildAt ρ 2 3 1 4 5 6))
    demoChan exampleProcess 0 6 7 [(4, predot (applyDot unifier pZero)), (5, predot (applyDot unifier y))] [8, 9]
    (fun σ solved => by
      rw [commit_label_old segRows segConf ρ 2 3 1 4 5 6 (by decide) (by decide) (by decide), segRows_zero]
      exact ReflNames.NameLaws.refl _)
    (fun σ solved => (reads σ solved).2.2.2)
    (fun q member σ solved => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with isFirst | isSecond
      · rw [isFirst]
        exact (reads σ solved).2.1
      · rw [isSecond]
        exact (reads σ solved).2.2.1)
    (fun o inside notOrder σ solved z same => by
      rcases (present₃ o).mp inside with ⟨inC, ne₂, ne₃, ne₁⟩ | is₄ | is₅ | is₆
      · rcases (inSeg o).mp inC with is₀ | is₁ | is₂ | is₃
        · rw [is₀, commit_label_old segRows segConf ρ 2 3 1 4 5 6 (by decide) (by decide) (by decide)] at same
          exact segRoot_not_child σ z same
        · exact ne₁ is₁
        · exact ne₂ is₂
        · exact ne₃ is₃
      · exact notOrder (by rw [is₄]; simp)
      · exact notOrder (by rw [is₅]; simp)
      · rw [is₆] at same
        have both := ((reads σ solved).2.2.2).symm.trans same
        rw [psubst_doneTok] at both
        exact absurd (nameLaws_heads both) (by decide))
    rfl (by decide)
    (fun o member inside => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases (present₃ o).mp inside with ⟨inC, -, -, -⟩ | is₄ | is₅ | is₆
      · rcases (inSeg o).mp inC with h | h | h | h <;> rcases member with m | m | m <;> rw [m] at h <;>
          exact absurd h (by decide)
      · rcases member with m | m | m <;> rw [m] at is₄ <;> exact absurd is₄ (by decide)
      · rcases member with m | m | m <;> rw [m] at is₅ <;> exact absurd is₅ (by decide)
      · rcases member with m | m | m <;> rw [m] at is₆ <;> exact absurd is₆ (by decide))
    ((present₃ 6).mpr (.inr (.inr (.inr rfl))))
    ((present₃ 0).mpr (.inl ⟨(inSeg 0).mpr (.inl rfl), by decide, by decide, by decide⟩))
    (by decide) (by decide) (by decide)
    (fun q member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with isFirst | isSecond
      · rw [isFirst]
        exact ⟨(present₃ 4).mpr (.inr (.inl rfl)), by decide⟩
      · rw [isSecond]
        exact ⟨(present₃ 5).mpr (.inr (.inr (.inl rfl))), by decide⟩)
    (solution_of_admitted committed)
  exact ⟨ρ, label₄, C₄, d', _, ρ₅, committed, coolRun, closed⟩

/-- **The reflection of the segment applies to every run of it** from the heated child of the example: the commit
is the source's COMM on the child's bag, and the made row reads as the listener of the dotted continuations. -/
theorem segment_reflects (ρ : PSubst) {label₄ : ℕ → Pattern} {C₄ : Configuration Pattern ℕ} {d' : ℕ}
    {rows : List Pattern} (ρ₅ : PSubst)
    (committed : (RuleSyntax.step QN ℕ QNE located).Admits (s := embed segRows segConf) (commChildAt ρ 2 3 1 4 5 6))
    (run : CoolRun exampleChild rootLoc (res segRows segConf (commChildAt ρ 2 3 1 4 5 6)).label
      (resConf segRows segConf (commChildAt ρ 2 3 1 4 5 6)) 6 label₄ C₄ d' rows)
    (closed : (RuleSyntax.step QN ℕ QNE located).Admits (s := embed label₄ C₄) (closeRootAt ρ₅ 0 d' 7)) :
    ∃ bs : Bindings,
      FiniteProgram.BagComm (pFor zeroTerm demoChan pZero ::ₘ pFor y demoChan y ::ₘ (([] : List (ℕ × Pattern)).map
          Prod.snd : Multiset Pattern))
        ((FiniteProgram.parts (applyDot bs pZero) : Multiset Pattern) +
          (FiniteProgram.parts (applyDot bs y) : Multiset Pattern) + (([] : List (ℕ × Pattern)).map Prod.snd :
            Multiset Pattern)) ∧
      ∀ σ : PSubst, nameAction.Models σ (res label₄ C₄ (closeRootAt ρ₅ 0 d' 7)).knowledge →
        NameLaws (psubst σ ((res label₄ C₄ (closeRootAt ρ₅ 0 d' 7)).label 7))
          (psubst σ (atLoc (pFor (tProc (pPar (([] : List (ℕ × Pattern)).map (fun q => predot q.2) ++
            [predot (applyDot bs pZero), predot (applyDot bs y)]))) demoChan pZero) rootLoc)) := by
  have inSeg : ∀ o, o ∈ segConf.present ↔ o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by
    intro o
    simp [segConf]
  obtain ⟨-, bs, bagComm, reads⟩ := refl_reflects segRows segConf demoChan exampleProcess 0 1 2 3 4 5 6 7 [] [] []
    zeroTerm y demoChan demoChan pZero y (by decide)
    (fun q member => by
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with isFirst | isSecond
      · rw [isFirst]
        exact ⟨(inSeg 2).mpr (.inr (.inr (.inl rfl))), by decide, fun σ _ =>
          nameLaws_of_eq (congrArg (psubst σ) segRows_two)⟩
      · rw [isSecond]
        exact ⟨(inSeg 3).mpr (.inr (.inr (.inr rfl))), by decide, fun σ _ =>
          nameLaws_of_eq (congrArg (psubst σ) segRows_three)⟩)
    (fun o inside notTk notCell σ _ z same => by
      rcases (inSeg o).mp inside with is₀ | is₁ | is₂ | is₃
      · rw [is₀] at same
        exact segRoot_not_child σ z same
      · exact notTk is₁
      · exact notCell (by rw [is₂]; simp)
      · exact notCell (by rw [is₃]; simp))
    (fun σ _ => by rw [segRows_one]; exact ReflNames.NameLaws.refl _)
    ((inSeg 0).mpr (.inl rfl)) (by decide) (by simp)
    (fun σ _ => by rw [segRows_zero]; exact ReflNames.NameLaws.refl _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ => ⟨unifier, unifier_groundPrincipal, unifier_values⟩) example_apart (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ρ committed run ρ₅ closed
  exact ⟨bs, bagComm, reads⟩

#print axioms segRoot_not_child
#print axioms segment_runs
#print axioms segment_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
