import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceReflect

/-!
# The REFL correspondence at the name frame: reflection of heating at the child

Before its step, a child `l` holds its token `Pending(l, m)` and its rows are cells (identity, source part), each
row reading as the represented part `predot P @ l`, no other row reading at `l` (`Cells`). Here, for EVERY heating
at the child (every admitted `heatChild` that reads the child's token), in every order:

* `heat_cell`: the heated row is a cell whose part is a binary parallel composition `a | b`; the result's cells
  replace it by two cells with the parts `a` and `b`; the invariant holds again, and the bag of the parts is the
  same modulo the bag laws;
* `heatRun_reflects`: along every run of such heatings, the invariant holds at the end and the bag of the parts is
  the starting bag modulo the bag laws.

The parts must heat as written (`Heatable`): binary compositions of parts that no substitution makes a binary
composition modulo the name laws (inputs, `0`, reflections; not bare variables).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (par pZero pPar)
open MeTTaOperationsComm (psubst PSubst)
open FiniteProgram (predot)
open OneFrame (embed)
open ReflQuotient (BagLaws BagAxiom)
open ReflNames (NameLaws nameAction QN QNE nameLaws_heads)
open ReflLocated (atLoc pendingTok located heatChildN heatChild_takes_pair heatChild_reads_determinately
  locatedFrame_name psubst_atLoc_any psubst_pendingTok)
open ReflLocatedStep (nameLaws_pendingTok_iff info_known res resConf)

variable {O : Type*}

theorem predot_par (a b : Pattern) : predot (par a b) = par (predot a) (predot b) := by
  simp [par, pPar, predot, FiniteProgram.predotList_eq_map]

/-- **Processes that heat as written**: binary compositions of such processes, or processes that no substitution
makes a binary composition modulo the name laws. -/
inductive Heatable : Pattern → Prop where
  | split {a b : Pattern} : Heatable a → Heatable b → Heatable (par a b)
  | solid {P : Pattern} : (∀ (σ : PSubst) (c d : Pattern), ¬ NameLaws (psubst σ (predot P)) (par c d)) → Heatable P

/-- **The child's cells before its step.** -/
structure Cells (l m : Pattern) (label : O → Pattern) (C : Configuration Pattern O) (tk : O)
    (cells : List (O × Pattern)) : Prop where
  token : tk ∈ C.present ∧ ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label tk)) (psubst σ (pendingTok l m))
  nodup : (cells.map Prod.fst).Nodup
  rows : ∀ q ∈ cells, q.1 ∈ C.present ∧ q.1 ≠ tk ∧ ∀ σ : PSubst, nameAction.Models σ C.equations →
    NameLaws (psubst σ (label q.1)) (psubst σ (atLoc (predot q.2) l))
  others : ∀ o ∈ C.present, o ≠ tk → o ∉ cells.map Prod.fst → ∀ σ : PSubst, nameAction.Models σ C.equations →
    ∀ y : Pattern, ¬ NameLaws (psubst σ (label o)) (atLoc y (psubst σ l))
  heatable : ∀ q ∈ cells, Heatable q.2

/-- **One heating at the child reflects a split of a cell.** -/
theorem heat_cell [DecidableEq O] {l m : Pattern} {label : O → Pattern} {C : Configuration Pattern O} {tk : O}
    {cells : List (O × Pattern)} (inv : Cells l m label C tk cells) (ρ : PSubst) (o m₁ m₂ : O)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (heatChildN ρ o tk m₁ m₂)) :
    ∃ cells' : List (O × Pattern),
      Cells l m (res label C (heatChildN ρ o tk m₁ m₂)).label (resConf label C (heatChildN ρ o tk m₁ m₂)) tk cells' ∧
      BagLaws (pPar (cells'.map Prod.snd)) (pPar (cells.map Prod.snd)) := by
  obtain ⟨_, shapes, enabled, ⟨_, w, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have oPresent : o ∈ C.present := enabled.taken_subset (by simp [heatChildN, Selection.commit])
  have freshM₁ : m₁ ∉ C.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (by simp [heatChildN, Selection.commit]) inside
  have freshM₂ : m₂ ∉ C.present := fun inside =>
    Finset.disjoint_left.mp enabled.fresh (by simp [heatChildN, Selection.commit]) inside
  have m₁m₂ : m₁ ≠ m₂ := by
    have nd := shapes.2.1
    simpa [heatChildN] using nd
  have known : nameAction.Models w C.equations := info_known _ solved
  obtain ⟨a, b, l', same, -, -, loc, tokenRead⟩ := heatChild_takes_pair label C ρ o tk m₁ m₂ solved
  have atL : NameLaws l' (psubst w l) := by
    have tk₁ := tokenRead.trans (inv.token.2 w known)
    rw [psubst_pendingTok] at tk₁
    exact loc.symm.trans (nameLaws_pendingTok_iff.mp tk₁).1
  have oTk : o ≠ tk := by
    intro isTk
    have both := inv.token.2 w known
    rw [← isTk, same, psubst_pendingTok] at both
    exact absurd (nameLaws_heads both) (by decide)
  have oCell : o ∈ cells.map Prod.fst := by
    by_contra notCell
    refine inv.others o oPresent oTk notCell w known (par a b) ?_
    rw [same]
    exact (locatedFrame_name.atLoc_iff _ _ _ _).mpr ⟨ReflNames.NameLaws.refl _, atL⟩
  obtain ⟨⟨o', P⟩, qIn, qFst⟩ := List.mem_map.mp oCell
  change o' = o at qFst
  subst qFst
  obtain ⟨s, t, cellsEq⟩ := List.append_of_mem qIn
  have rowO : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label o')) (psubst σ (atLoc (predot P) l)) := (inv.rows (o', P) qIn).2.2
  have heatP : Heatable P := inv.heatable (o', P) qIn
  cases heatP with
  | solid notPair =>
      have read := rowO w known
      rw [same, psubst_atLoc_any] at read
      exact absurd ((locatedFrame_name.atLoc_iff _ _ _ _).mp read).1.symm (notPair w a b)
  | @split a₀ b₀ heatA heatB =>
      have readsTaken : ∀ σ : PSubst, nameAction.Models σ C.equations →
          NameLaws (psubst σ (label o')) (psubst σ (atLoc (par (predot a₀) (predot b₀)) l)) := by
        intro σ solvedσ
        have read := rowO σ solvedσ
        rw [predot_par] at read
        exact read
      have permCells : cells.Perm ((o', par a₀ b₀) :: (s ++ t)) := by
        rw [cellsEq]
        exact List.perm_middle
      obtain ⟨oOut, restNodup⟩ := List.nodup_cons.mp ((permCells.map Prod.fst).nodup_iff.mp inv.nodup)
      have restIn : ∀ q ∈ s ++ t, q ∈ cells := fun q inside => permCells.symm.subset (List.mem_cons.mpr (.inr inside))
      have restNotO : ∀ q ∈ s ++ t, q.1 ≠ o' := fun q inside same' =>
        oOut (same' ▸ List.mem_map.mpr ⟨q, inside, rfl⟩)
      have cellFresh : ∀ q ∈ cells, q.1 ≠ m₁ ∧ q.1 ≠ m₂ := fun q inside =>
        ⟨fun same' => freshM₁ (same' ▸ (inv.rows q inside).1), fun same' => freshM₂ (same' ▸ (inv.rows q inside).1)⟩
      have tkIn : tk ∈ C.present := inv.token.1
      have tkM₁ : tk ≠ m₁ := fun same' => freshM₁ (same' ▸ tkIn)
      have tkM₂ : tk ≠ m₂ := fun same' => freshM₂ (same' ▸ tkIn)
      have back : ∀ σ : PSubst, nameAction.Models σ (resConf label C (heatChildN ρ o' tk m₁ m₂)).equations →
          nameAction.Models σ C.equations := fun σ solvedσ => heat_back label C ρ o' tk m₁ m₂ solvedσ
      refine ⟨s ++ (m₁, a₀) :: (m₂, b₀) :: t, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · refine ⟨(heat_present label C ρ o' tk m₁ m₂ tk).mpr (.inl ⟨tkIn, Ne.symm oTk⟩), fun σ solvedσ => ?_⟩
        rw [heat_label_old label C ρ o' tk m₁ m₂ tkM₁ tkM₂]
        exact inv.token.2 σ (back σ solvedσ)
      · have perm : ((s ++ (m₁, a₀) :: (m₂, b₀) :: t).map Prod.fst).Perm
            (m₁ :: m₂ :: (s ++ t).map Prod.fst) := by
          simp only [List.map_append, List.map_cons]
          refine List.perm_middle.trans (List.Perm.cons _ ?_)
          exact List.perm_middle
        refine perm.nodup_iff.mpr (List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, restNodup⟩⟩)
        · intro inside
          rcases List.mem_cons.mp inside with same' | inRest
          · exact m₁m₂ same'
          · obtain ⟨q, inQ, same'⟩ := List.mem_map.mp inRest
            exact (cellFresh q (restIn q inQ)).1 same'
        · intro inRest
          obtain ⟨q, inQ, same'⟩ := List.mem_map.mp inRest
          exact (cellFresh q (restIn q inQ)).2 same'
      · intro q member
        have cases' : q ∈ s ++ t ∨ q = (m₁, a₀) ∨ q = (m₂, b₀) := by
          simp only [List.mem_append, List.mem_cons] at member ⊢
          rcases member with inS | isM₁ | isM₂ | inT
          · exact .inl (.inl inS)
          · exact .inr (.inl isM₁)
          · exact .inr (.inr isM₂)
          · exact .inl (.inr inT)
        rcases cases' with inRest | isM₁ | isM₂
        · obtain ⟨present', notTk, reads'⟩ := inv.rows q (restIn q inRest)
          obtain ⟨ne₁, ne₂⟩ := cellFresh q (restIn q inRest)
          refine ⟨(heat_present label C ρ o' tk m₁ m₂ q.1).mpr (.inl ⟨present', restNotO q inRest⟩), notTk,
            fun σ solvedσ => ?_⟩
          rw [heat_label_old label C ρ o' tk m₁ m₂ ne₁ ne₂]
          exact reads' σ (back σ solvedσ)
        · rw [isM₁]
          exact ⟨(heat_present label C ρ o' tk m₁ m₂ m₁).mpr (.inr (.inl rfl)), Ne.symm tkM₁, fun σ solvedσ =>
            (heatChild_reads_determinately label C ρ o' tk m₁m₂ (predot a₀) (predot b₀) l readsTaken solvedσ).1⟩
        · rw [isM₂]
          exact ⟨(heat_present label C ρ o' tk m₁ m₂ m₂).mpr (.inr (.inr rfl)), Ne.symm tkM₂, fun σ solvedσ =>
            (heatChild_reads_determinately label C ρ o' tk m₁m₂ (predot a₀) (predot b₀) l readsTaken solvedσ).2⟩
      · intro o'' inside notTk notCell σ solvedσ y same'
        rcases (heat_present label C ρ o' tk m₁ m₂ o'').mp inside with ⟨inC, notO⟩ | isM₁ | isM₂
        · have ne₁ : o'' ≠ m₁ := fun e => freshM₁ (e ▸ inC)
          have ne₂ : o'' ≠ m₂ := fun e => freshM₂ (e ▸ inC)
          rw [heat_label_old label C ρ o' tk m₁ m₂ ne₁ ne₂] at same'
          refine inv.others o'' inC notTk ?_ σ (back σ solvedσ) y same'
          intro inCells
          obtain ⟨q, inQ, same''⟩ := List.mem_map.mp inCells
          rcases List.mem_cons.mp (permCells.subset inQ) with isQ | inRest
          · exact notO (by rw [← same'', isQ])
          · apply notCell
            rw [← same'']
            exact List.mem_map.mpr ⟨q, by simp only [List.mem_append, List.mem_cons] at inRest ⊢; tauto, rfl⟩
        · exact notCell (by rw [isM₁]; simp)
        · exact notCell (by rw [isM₂]; simp)
      · intro q member
        simp only [List.mem_append, List.mem_cons] at member
        rcases member with inS | isM₁ | isM₂ | inT
        · exact inv.heatable q (restIn q (List.mem_append_left _ inS))
        · rw [isM₁]
          exact heatA
        · rw [isM₂]
          exact heatB
        · exact inv.heatable q (restIn q (List.mem_append_right _ inT))
      · rw [cellsEq]
        simp only [List.map_append, List.map_cons]
        have flat := BagLaws.of_axiom (BagAxiom.flatten (s.map Prod.snd) [a₀, b₀] (t.map Prod.snd))
        simp only [List.append_assoc, List.cons_append, List.nil_append] at flat
        exact flat.symm

/-- **A run of heatings at the child**: every firing heats a row reading the child's token `tk`. -/
inductive HeatRun [DecidableEq O] (tk : O) :
    (O → Pattern) → Configuration Pattern O → (O → Pattern) → Configuration Pattern O → Prop where
  | refl (label : O → Pattern) (C : Configuration Pattern O) : HeatRun tk label C label C
  | step {label : O → Pattern} {C : Configuration Pattern O} {label' : O → Pattern} {C' : Configuration Pattern O}
      (ρ : PSubst) (o m₁ m₂ : O)
      (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C) (heatChildN ρ o tk m₁ m₂))
      (rest : HeatRun tk (res label C (heatChildN ρ o tk m₁ m₂)).label (resConf label C (heatChildN ρ o tk m₁ m₂))
        label' C') : HeatRun tk label C label' C'

/-- **Every heating run at the child reflects**: the cells' invariant holds at its end, and the bag of the parts
is the starting bag modulo the bag laws, in whatever order the run split. -/
theorem heatRun_reflects [DecidableEq O] {l m : Pattern} {tk : O} {label label' : O → Pattern}
    {C C' : Configuration Pattern O} (run : HeatRun tk label C label' C') :
    ∀ {cells : List (O × Pattern)}, Cells l m label C tk cells →
      ∃ cells' : List (O × Pattern), Cells l m label' C' tk cells' ∧
        BagLaws (pPar (cells'.map Prod.snd)) (pPar (cells.map Prod.snd)) := by
  induction run with
  | refl label C => exact fun inv => ⟨_, inv, BagLaws.refl _⟩
  | step ρ o m₁ m₂ admitted rest ih =>
      intro cells inv
      obtain ⟨cells₁, inv₁, bag₁⟩ := heat_cell inv ρ o m₁ m₂ admitted
      obtain ⟨cells₂, inv₂, bag₂⟩ := ih inv₁
      exact ⟨cells₂, inv₂, bag₂.trans bag₁⟩

#print axioms predot_par
#print axioms heat_cell
#print axioms heatRun_reflects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
