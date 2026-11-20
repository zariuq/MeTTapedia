import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Toolkit

/-!
# Spaces: creation, addition seen by a later query, removal, multiplicity

`(new-space &s (add-atom &s (fact 1) (add-atom &s (fact 2) (add-atom &s (fact 2)
  (remove-atom &s (fact 1) (match &s (fact $v) $v))))))`

A fresh space is created and bound to `&s`; three rows are added, `(fact 2)` twice; `(fact 1)` is
removed by unification; the query then sees the two rows added before it and not the removed one.
The bag of answers is `{2, 2}`: the additions are seen, the removal is seen, and the multiplicity of the
stored rows is kept (`spaces_example`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleSpaces

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit

/-- The trivial discipline, written out so that its type language is `MTy` on the nose. -/
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩

def program : Program mkeys [] () MTy := ⟨[], fun t => .apply t⟩

/-- Fresh handles. -/
def supply : ℕ → MClosed := fun n => ctuple [csym "space", cnum n]

def fact (n : Int) : MData := tuple [sym "fact", num n]

def s0 : MData := foD [] [10] 0
def v : MData := foD [] [9] 0

def query : Comp mkeys [] () MTy :=
  .new [10] s0 (.add s0 (fact 1) (.add s0 (fact 2) (.add s0 (fact 2)
    (.remove s0 (fact 1) (.query s0 (tuple [sym "fact", v]) (.ret v))))))

/-- The handle of the space. -/
def h0 : MClosed := supply 0

/-- The opened name of the space. -/
def s : MData := foD [0] [10] 0

/-- The store after creating the space. -/
def K0 : List (Constraint mkeys [] ()) := [(s, Rigid.includeTerm (fam mkeys) h0)]

def r1 : Row mkeys [] () := ⟨fact 1, K0⟩
def r2 : Row mkeys [] () := ⟨fact 2, K0⟩

def K1 : List (Constraint mkeys [] ()) := K0 ++ rowUse 1 r1 (fact 1)
def K2 : List (Constraint mkeys [] ()) := K1 ++ rowUse 2 r2 (tuple [sym "fact", v])

/-- A solution of the final store. -/
def σ : Assignment (fam mkeys) noNames := fun x =>
  match x with
  | ⟨[], ⟨[9], 0, ([], ())⟩⟩ => Rigid.includeTerm noNames (cnum 2)
  | ⟨_, ⟨_, _, (_, _)⟩⟩ => Rigid.includeTerm noNames (rename (Γ := []) (fun _ impossible => nomatch impossible) h0)

theorem K2_solved : Models σ K2 := by
  intro e member
  simp only [K2, K1, K0, rowUse, copyStore, r1, r2, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem K2_live : Solvable K2 := ⟨Empty, noNames, σ, K2_solved⟩
theorem K1_live : Solvable K1 := solvable_of_append K2_live
theorem K0_live : Solvable K0 := solvable_of_append K1_live

theorem K0_determines : Determines K0 s h0 :=
  ⟨K0_live, fun _ _ solved => (solved _ (List.mem_singleton_self _)).trans (Rigid.instantiate_include _ h0)⟩

/-! ## The world along the run -/

noncomputable def S1 :=
  setSpace (fun _ => 0) h0 ((fun _ : MClosed => (0 : Multiset (Row mkeys [] ()))) h0 + {⟨fact 1, K0⟩})
noncomputable def S2 := setSpace S1 h0 (S1 h0 + {⟨fact 2, K0⟩})
noncomputable def S3 := setSpace S2 h0 (S2 h0 + {⟨fact 2, K0⟩})
noncomputable def S4 := setSpace S3 h0 ({r2, r2} : Multiset (Row mkeys [] ()))

theorem S3_at : S3 h0 = r1 ::ₘ {r2, r2} := by
  simp only [S3, S2, S1, setSpace_same, zero_add, r1, r2]
  rfl

theorem S4_at : S4 h0 = {r2, r2} := setSpace_same _ _ _

/-- The alternative made by one row of the query. -/
def found : Branch mkeys [] () MTy := ⟨K2, .eval (.ret v), [], []⟩
def answered : Branch mkeys [] () MTy := ⟨K2, .value v, [], []⟩

noncomputable def final : Config mkeys [] () MTy :=
  ⟨⟨3, 1, S4⟩, answered ::ₘ answered ::ₘ 0⟩

theorem runs : Runs D program supply (Config.initial (fun _ => 0) query) final := by
  show Runs D program supply _ ⟨⟨3, 1, S4⟩, answered ::ₘ answered ::ₘ 0⟩
  -- the two alternatives return
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 1, S4⟩, found ::ₘ answered ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := found) (rest := answered ::ₘ 0)
      (bs := answered ::ₘ 0) rfl
      (Multiset.singleton_add _ _).symm K2_live (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨⟨3, 1, S4⟩, found ::ₘ found ::ₘ 0⟩) ?_
    (Step.of_eq (D := D) (P := program) (supply := supply) (b := found) (rest := found ::ₘ 0)
      (bs := answered ::ₘ 0) rfl
      (by rw [Multiset.cons_add, zero_add, Multiset.cons_swap]) K2_live (.ret _ _ _ _ _))
  -- the query: one alternative per stored row
  refine Relation.ReflTransGen.tail (b := ⟨⟨2, 1, S4⟩, {⟨K1, .eval (.query s (tuple [sym "fact", v]) (.ret v)), [], []⟩}⟩) ?_
    (Step.of_eq (rest := 0) rfl (by dsimp only; rw [S4_at]; rfl) K1_live
      (.query _ _ _ _ _ _ _ h0 (Determines.extend K0_determines K1_live)))
  -- the removal of `(fact 1)`
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, S3⟩, {⟨K0, .eval (.remove s (fact 1)
      (.query s (tuple [sym "fact", v]) (.ret v))), [], []⟩}⟩) ?_
    (step_one K0_live (.remove ⟨1, 1, S3⟩ K0 s (fact 1) (.query s (tuple [sym "fact", v]) (.ret v)) [] [] h0
      K0_determines r1 {r2, r2} S3_at K1_live))
  -- the three additions
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, S2⟩, {⟨K0, .eval (.add s (fact 2) (.remove s (fact 1)
      (.query s (tuple [sym "fact", v]) (.ret v)))), [], []⟩}⟩) ?_
    (step_one K0_live (.add _ _ _ _ _ _ _ h0 K0_determines))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, S1⟩, {⟨K0, .eval (.add s (fact 2) (.add s (fact 2)
      (.remove s (fact 1) (.query s (tuple [sym "fact", v]) (.ret v))))), [], []⟩}⟩) ?_
    (step_one K0_live (.add _ _ _ _ _ _ _ h0 K0_determines))
  refine Relation.ReflTransGen.tail (b := ⟨⟨1, 1, fun _ => 0⟩, {⟨K0, .eval (.add s (fact 1) (.add s (fact 2)
      (.add s (fact 2) (.remove s (fact 1) (.query s (tuple [sym "fact", v]) (.ret v)))))), [], []⟩}⟩) ?_
    (step_one K0_live (.add _ _ _ _ _ _ _ h0 K0_determines))
  -- the creation of the space
  exact Relation.ReflTransGen.single (step_one live_nil (.new _ _ _ _ _ _ _))

/-- Every solution of the final store reads `$v` as `2`. -/
theorem final_determines : Determines K2 v (cnum 2) := by
  refine ⟨K2_live, fun target σ' solved => ?_⟩
  have last := solved (tuple [sym "fact", v], instantiate (copyAt mkeys 2) r2.atom)
    (List.mem_append_right K1 (List.mem_append_right _ (List.mem_singleton_self _)))
  have pair : tupleAt [symAt "fact", σ' (fo [] [9] 0)] = tupleAt [symAt "fact", Rigid.includeTerm target (cnum 2)] := by
    rw [← instantiate_foD σ' [] [9] 0]
    exact last
  show instantiate σ' (foD [] [9] 0) = _
  rw [instantiate_foD]
  exact (tuple2_inj pair).2

theorem answered_finished : Branch.Finished (D := D) answered := ⟨rfl, _, rfl⟩

/-- **The bag of answers**: `{2, 2}`. -/
theorem spaces_answers : Config.answers (D := D) final = {{cnum 2}, {cnum 2}} := by
  have one : Branch.answer (D := D) answered = {cnum 2} := answer_of_determines rfl final_determines
  have first := answers_cons_finished (D := D) (w := ⟨3, 1, S4⟩) (rest := answered ::ₘ 0)
    answered_finished K2_live
  have second := answers_cons_finished (D := D) (w := ⟨3, 1, S4⟩) (rest := 0) answered_finished K2_live
  rw [answers_zero] at second
  rw [second, one] at first
  exact first

theorem spaces_example :
    ∃ C, Runs D program supply (Config.initial (fun _ => 0) query) C ∧
      Config.Quiescent (D := D) program supply C ∧ Config.answers (D := D) C = {{cnum 2}, {cnum 2}} := by
  refine ⟨final, runs, ?_, spaces_answers⟩
  intro b member _ w' bs moved
  have member' : b ∈ answered ::ₘ answered ::ₘ 0 := member
  have only : b = ⟨K2, .value v, [], []⟩ := by
    rcases Multiset.mem_cons.mp member' with same | rest
    · exact same
    · rcases Multiset.mem_cons.mp rest with same | none
      · exact same
      · cases none
  subst only
  cases moved

#print axioms spaces_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleSpaces
