import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramUnmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedControls

/-!
# Controls for unmatched calls as values, with versions

Version `1` has no equation for `f`; version `2` installs `(= (f a) b)`.

* **Answered as itself under version 1** (`answered_as_itself_v1`, `…_on_step`): `(f a)` returns
  the data `(f a)`, citing version `1`.
* **Reduced under version 2** (`reduced_v2`, `…_on_step`): `(f a)` returns `b`, citing version `2`.
  The absence query refuses the unmatched firing there (`unmatched_refused_v2`): a matching
  equation is seen at the cut.
* **No retroactive change** (`no_retroactive_change`, `…_on_step`): `(f a)` is answered under
  version `1`, then version `2` is installed; the answer `(f a)` and its citation of version `1`
  stay. The recheck of that answer passes against version `1` and fails against version `2`
  (`recheck_control`), which is what a later version changes: the recheck, not the answer.
* **The outer call proceeds with an unmatched inner call as its argument**
  (`inner_value_outer_call`, `…_on_step`): with `(= (g a) b)` and `(= (f $x) (out $x))`, the inner
  call `(g c)` of `(f (g c))` matches nothing and becomes the value `(g c)`; the outer call then
  matches and gives `(out (g c))`. Without the unmatched rule the same call stays waiting
  (`ProgramNested.Controls.unmatched_inner_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.UnmatchedControls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.Controls

/-- `(= (f a) b)`. -/
def eqFa : NEquation := ⟨.cell (.sym 150) (.sym 152), .val (.sym 153)⟩

/-- Version `2` installs `(= (f a) b)`; every other version has no equation. -/
def defsV : Defs := fun u => if u = 2 then [eqFa] else []

/-- The call `(f a)`. -/
def faCall : Ex := callOf sf (gv sa)

theorem faCall_ground : GroundEx faCall := ⟨⟨sf, rfl⟩, ⟨sa, rfl⟩⟩

/-- The data `(f a)`. -/
def fa : Tm := node (embed sf) (embed sa)

theorem lift {defs : Defs} {a b : Multiset SRow × ℕ} (run : Relation.ReflTransGen (KStep defs) a b) :
    Relation.ReflTransGen (UStep defs) a b := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.machine step)

/-- From `(f a)`, seven administrative steps reach the call of the data `(f a)`. -/
theorem fa_run (defs : Defs) (F : Multiset SRow) (n : ℕ) :
    Relation.ReflTransGen (KStep defs) (.ev faCall [] ::ₘ F, n) (.ap fa [] ::ₘ F, n + 7) := by
  have s1 := KStep.call (defs := defs) (.pair (gv sf) (gv sa)) [] F n
  have s2 := KStep.pair (defs := defs) (gv sf) (gv sa) [.arg] F (n + 1)
  have s3 := KStep.val (defs := defs) (embed sf) [.left (gv sa), .arg] F (n + 2)
  have s4 := KStep.left (defs := defs) (embed sf) (gv sa) [.arg] F (n + 3)
  have s5 := KStep.val (defs := defs) (embed sa) [.right (embed sf), .arg] F (n + 4)
  have s6 := KStep.right (defs := defs) (embed sf) (embed sa) [.arg] F (n + 5)
  have s7 := KStep.arg (defs := defs) (node (embed sf) (embed sa)) [] F (n + 6)
  exact ((((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6).tail s7

theorem v1_empty : defsV 1 = [] := rfl

theorem none_v1 (n : ℕ) (w : Tm) : ∀ e ∈ defsV 1, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at n, w)] := by
  intro e member
  rw [v1_empty] at member
  cases member

/-- **Answered as itself under version 1.** -/
theorem answered_as_itself_v1 :
    Relation.ReflTransGen (UStep defsV) (.ev faCall [] ::ₘ .version 1 ::ₘ 0, 1)
      (.ret fa [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0, 9) :=
  (lift (fa_run defsV (.version 1 ::ₘ 0) 1)).tail (.unmatched 1 fa [] 0 8 (none_v1 8 fa))

theorem answered_as_itself_v1_on_step :
    ∃ D, Relation.ReflTransGen (UTranslated defsV)
      (openInitial ([SRow.ev faCall [], .version 1].map SRow.enc), 1) (D, 9) ∧
      ORepresents D ((.ret fa [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0 : Multiset SRow).map SRow.enc) 9 :=
  (u_execution defsV _ (start_good _ 1) (start_bounded faCall_ground 1) _ 9).1 answered_as_itself_v1

/-- **Reduced under version 2.** -/
theorem reduced_v2 :
    Relation.ReflTransGen (UStep defsV) (.ev faCall [] ::ₘ .version 2 ::ₘ 0, 1)
      (.ret (embed sb) [] ::ₘ .citation 2 ::ₘ .version 2 ::ₘ 0, 10) := by
  have s8 := KStep.apply (defs := defsV) 2 ⟨0, by decide⟩ fa [] 0 8 (Subst.id rows)
    (mgu_ground 8 eqFa.lhs (.cell sf sa) rfl)
  have rhs : (((defsV 2).get ⟨0, by decide⟩).rhs.at 8).subst (Subst.id rows) = gv sb := rfl
  rw [rhs, List.map_nil, Multiset.map_zero] at s8
  have s9 := KStep.val (defs := defsV) (embed sb) [] (.citation 2 ::ₘ .version 2 ::ₘ 0) 9
  exact ((lift (fa_run defsV (.version 2 ::ₘ 0) 1)).tail (.machine s8)).tail (.machine s9)

theorem reduced_v2_on_step :
    ∃ D, Relation.ReflTransGen (UTranslated defsV)
      (openInitial ([SRow.ev faCall [], .version 2].map SRow.enc), 1) (D, 10) ∧
      ORepresents D ((.ret (embed sb) [] ::ₘ .citation 2 ::ₘ .version 2 ::ₘ 0 : Multiset SRow).map SRow.enc)
        10 :=
  (u_execution defsV _ (start_good _ 2) (start_bounded faCall_ground 2) _ 10).1 reduced_v2

/-- `(= (f a) b)` unifies with the data `(f a)`. -/
theorem fa_matches (n : ℕ) : ¬ UnmatchedRecheck defsV 2 n fa := fun recheck =>
  recheck eqFa (by simp [defsV]) (Subst.id rows) (fun e member => by
    rw [List.mem_singleton] at member
    rw [member]
    rfl)

/-- **The absence query refuses the unmatched firing under version 2**, wherever the call and the
version row are represented. -/
theorem unmatched_refused_v2 {C : Config} {n : ℕ} {μ : Subst rows} (solved : SolvedForm C n μ)
    {F : Multiset SRow} (image : C.present.val.map (readAt μ) = (.ap fa [] ::ₘ .version 2 ::ₘ F).map SRow.enc)
    {o o' : Occ} (oIn : o ∈ C.present) (o'In : o' ∈ C.present) (apart : o ≠ o')
    (reads : readAt μ o = (SRow.ap fa []).enc) (reads' : readAt μ o' = (SRow.version 2).enc) :
    ¬ (unmatchedFiring defsV 2 n [o] [o']).Valid A Occ.label C := fun valid =>
  fa_matches n ((unmatched_fire solved image oIn o'In apart rfl reads reads').1.mp valid)

/-- **The recheck of the answer `(f a)`**: it passes against version `1` and fails against
version `2`. -/
theorem recheck_control (n : ℕ) : UnmatchedRecheck defsV 1 n fa ∧ ¬ UnmatchedRecheck defsV 2 n fa :=
  ⟨none_v1 n fa, fa_matches n⟩

/-- The final rows of the run with a later redefinition. -/
def afterRows : Multiset SRow := .finished ::ₘ .version 2 ::ₘ .ret fa [] ::ₘ .citation 1 ::ₘ 0

/-- **No retroactive change**: `(f a)` is answered as itself under version `1`; installing version
`2` afterwards leaves the answer and its citation of version `1` in place. -/
theorem no_retroactive_change :
    Relation.ReflTransGen (UStep defsV) (.ev faCall [] ::ₘ .version 1 ::ₘ .redef 2 ::ₘ 0, 1)
      (afterRows, 10) := by
  have answered := (lift (fa_run defsV (.version 1 ::ₘ .redef 2 ::ₘ 0) 1)).tail
    (.unmatched 1 fa [] (.redef 2 ::ₘ 0) 8 (none_v1 8 fa))
  have reorder : SRow.ret fa [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ .redef 2 ::ₘ 0 =
      .redef 2 ::ₘ .version 1 ::ₘ .ret fa [] ::ₘ .citation 1 ::ₘ 0 := by
    rw [Multiset.cons_swap (SRow.version 1) (SRow.redef 2),
      Multiset.cons_swap (SRow.citation 1) (SRow.redef 2),
      Multiset.cons_swap (SRow.ret fa []) (SRow.redef 2),
      Multiset.cons_swap (SRow.citation 1) (SRow.version 1),
      Multiset.cons_swap (SRow.ret fa []) (SRow.version 1)]
  rw [reorder] at answered
  exact answered.tail (redefinition_keeps_other_rows (u := 1) (u' := 2))

theorem no_retroactive_change_on_step :
    ∃ D, Relation.ReflTransGen (UTranslated defsV)
      (openInitial ([SRow.ev faCall [], .version 1, .redef 2].map SRow.enc), 1) (D, 10) ∧
      ORepresents D (afterRows.map SRow.enc) 10 := by
  have good : ∀ s ∈ [SRow.ev faCall [], .version 1, .redef 2], s.Good := by
    intro s h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> trivial
  have bounded : ∀ s ∈ [SRow.ev faCall [], .version 1, .redef 2], Bounded 1 s.enc := by
    intro s h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact btag (bnode (faCall_ground.bounded 1) (bconst 1 143))
    · exact btag (bconst 1 1)
    · exact btag (bconst 1 2)
  exact (u_execution defsV _ good bounded _ 10).1 no_retroactive_change

/-! ## The outer call proceeds with an unmatched inner call -/

/-- The data `(g c)`. -/
def gc : Tm := embed (.cell sg sc)

/-- **With unmatched calls as values, `(f (g c))` gives `(out (g c))`.** -/
theorem inner_value_outer_call :
    Relation.ReflTransGen (UStep defsFG) (.ev (nestedExpr sc) [] ::ₘ .version 1 ::ₘ 0, 1)
      (.ret (node (embed sout) gc) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0, 17) := by
  have reached := (lift (inner_run defsFG sc (.version 1 ::ₘ 0) 1)).tail
    (.unmatched 1 gc outerFrames 0 12 (no_equation_unifies 12))
  have s13 := KStep.right (defs := defsFG) (embed sf) gc [.arg] (.citation 1 ::ₘ .version 1 ::ₘ 0) 13
  have s14 := KStep.arg (defs := defsFG) (node (embed sf) gc) [] (.citation 1 ::ₘ .version 1 ::ₘ 0) 14
  have reorder : SRow.ap (node (embed sf) gc) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ 0 =
      .ap (node (embed sf) gc) [] ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0 := by
    rw [Multiset.cons_swap (SRow.citation 1)]
  rw [reorder] at s14
  have mgu15 : IsMGU [(eqF.lhs.at 15, node (embed sf) gc)] (matcher 15 [gc]) :=
    matcher_isMGU (n := 15) (vals := [gc]) (fun t h => by
      rw [List.mem_singleton] at h
      rw [h]
      exact embed_bounded 15 _) (p := eqF.lhs) (by decide) (by decide)
  have s15 := KStep.apply (defs := defsFG) 1 ⟨1, by decide⟩ (node (embed sf) gc) [] (.citation 1 ::ₘ 0) 15
    (matcher 15 [gc]) mgu15
  have rhs15 : (((defsFG 1).get ⟨1, by decide⟩).rhs.at 15).subst (matcher 15 [gc]) =
      .val (node (embed sout) gc) := by
    show Ex.val ((matcher 15 [gc]).applyTerm ((Pat.cell (.sym 155) (.var 0)).at 15)) = _
    rw [matcher_at _ (by decide)]
    rfl
  rw [rhs15, List.map_nil, rows_fixed _ _ (by
    intro s h
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at h
    rw [h]
    rfl)] at s15
  have s16 := KStep.val (defs := defsFG) (node (embed sout) gc) []
    (.citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0) 16
  exact (((reached.tail (.machine s13)).tail (.machine s14)).tail (.machine s15)).tail (.machine s16)

theorem inner_value_outer_call_on_step :
    ∃ D, Relation.ReflTransGen (UTranslated defsFG)
      (openInitial ([SRow.ev (nestedExpr sc) [], .version 1].map SRow.enc), 1) (D, 17) ∧
      ORepresents D ((.ret (node (embed sout) gc) [] ::ₘ .citation 1 ::ₘ .version 1 ::ₘ .citation 1 ::ₘ 0 :
        Multiset SRow).map SRow.enc) 17 :=
  (u_execution defsFG _ (start_good _ 1) (start_bounded (nestedExpr_ground sc) 1) _ 17).1
    inner_value_outer_call

#print axioms fa_run
#print axioms answered_as_itself_v1
#print axioms answered_as_itself_v1_on_step
#print axioms reduced_v2
#print axioms reduced_v2_on_step
#print axioms fa_matches
#print axioms unmatched_refused_v2
#print axioms recheck_control
#print axioms no_retroactive_change
#print axioms no_retroactive_change_on_step
#print axioms inner_value_outer_call_on_step
#print axioms inner_value_outer_call

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.UnmatchedControls
