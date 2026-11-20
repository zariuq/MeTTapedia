import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NestedCore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedComplete

/-!
# A call that no equation answers: stuck in the nested-calls core, data in the language

The program `(= 1 2)` of the nested-calls core, and the queries `(call 5)` and `(call 1)`.

* **The core has no step** from `(call 5)` (`core_stuck`): its only redex is the call, and no
  left-hand side unifies with `5`. From `(call 1)` it answers `2` in one step (`core_matched`).
* **The language, on the embedding** (`NestedCore.program`), returns the call that no equation
  answers as data: the run from `(call 5)` ends, with no live alternative left to move, with the bag
  `{5}` (`inert_example`).
* **With the failing equation added last** (`NestedCore.programStrict`), the run from `(call 5)` ends
  with no live alternative and the empty bag (`strict_example`), as in the core, and the run from
  `(call 1)` still ends with the bag `{2}` (`strict_matched_example`): the failing equation removes no
  answer of a call that an equation answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleStuckCall

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NestedCore

/-! ## The core: stuck at `(call 5)`, one step at `(call 1)` -/

/-- The program `(= 1 2)` of the nested-calls core. -/
def eqs : List ProgramNested.NEquation := [⟨.sym 1, .val (.sym 2)⟩]

/-- The core's configuration of the query `(call k)`. -/
def src (k : ℕ) : Multiset ProgramRows.Tm :=
  ProgramEquations.thread (ProgramNested.encE (.call (.val (.const k)))) ::ₘ
    ProgramEquations.Versions.ver 0 ::ₘ 0

theorem no_second_thread (y : ProgramRows.Tm) (cs : Multiset ProgramRows.Tm) :
    ProgramEquations.Versions.ver 0 ::ₘ 0 ≠ ProgramEquations.thread y ::ₘ cs := by
  intro same
  rcases Multiset.cons_eq_cons.mp same with ⟨first, _⟩ | ⟨_, cs', first, _⟩
  · rw [ProgramEquations.Versions.ver, ProgramEquations.thread, ProgramEquations.tagged_inj] at first
    exact absurd first.1 (by decide)
  · exact Multiset.cons_ne_zero first.symm

/-- **The core is stuck at `(call 5)`.** -/
theorem core_stuck (s' : Multiset ProgramRows.Tm × ℕ) :
    ¬ ProgramNested.CStep (fun _ => eqs) (src 5, 0) s' := by
  intro step
  generalize start : ((src 5, 0) : Multiset ProgramRows.Tm × ℕ) = c at step
  cases step with
  | build E v w F n =>
      have rows := congrArg Prod.fst start
      simp only [src] at rows
      rcases Multiset.cons_eq_cons.mp rows with ⟨same, _⟩ | ⟨_, cs, second, _⟩
      · have filled := ProgramNested.encE_inj (ProgramNested.thread_inj same)
        cases E with
        | hole => simp [ProgramNested.ECtx.fill] at filled
        | pairL E b => simp [ProgramNested.ECtx.fill] at filled
        | pairR v' E => simp [ProgramNested.ECtx.fill] at filled
        | arg E =>
            simp only [ProgramNested.ECtx.fill, ProgramNested.Ex.call.injEq] at filled
            exact ProgramNested.fill_redex_not_value (.inl ⟨v, w, rfl⟩) E ⟨_, filled.symm⟩
      · exact no_second_thread _ cs second
  | apply u j E w F n m fresh θ mgu =>
      have rows := congrArg Prod.fst start
      simp only [src] at rows
      rcases Multiset.cons_eq_cons.mp rows with ⟨same, _⟩ | ⟨_, cs, second, _⟩
      · have filled := ProgramNested.encE_inj (ProgramNested.thread_inj same)
        cases E with
        | hole =>
            simp only [ProgramNested.ECtx.fill, ProgramNested.Ex.call.injEq,
              ProgramNested.Ex.val.injEq] at filled
            subst filled
            obtain ⟨index, bound⟩ := j
            have zero : index = 0 := by simp [eqs] at bound; omega
            subst zero
            have unified := mgu.unifies _ (List.mem_singleton.mpr rfl)
            simp [eqs, ProgramRows.Pat.at, Mettapedia.Logic.LP.Subst.applyTerm] at unified
        | pairL E b => simp [ProgramNested.ECtx.fill] at filled
        | pairR v' E => simp [ProgramNested.ECtx.fill] at filled
        | arg E =>
            simp only [ProgramNested.ECtx.fill, ProgramNested.Ex.call.injEq] at filled
            exact ProgramNested.fill_redex_not_value (.inr ⟨w, rfl⟩) E ⟨_, filled.symm⟩
      · exact no_second_thread _ cs second
  | redefine u u' F n =>
      have rows := congrArg Prod.fst start
      simp only [src] at rows
      rcases Multiset.cons_eq_cons.mp rows with ⟨same, _⟩ | ⟨_, cs, second, _⟩
      · have inner := ProgramNested.thread_inj same
        rw [ProgramEquations.Versions.redefTo, ProgramNested.encE, ProgramEquations.tagged_inj] at inner
        exact absurd inner.1 (by decide)
      · exact no_second_thread _ cs second

/-- **The core answers `(call 1)` with `2` in one step.** -/
theorem core_matched :
    ProgramNested.CStep (fun _ => eqs) (src 1, 0)
      (ProgramEquations.thread (ProgramNested.encE (.val (.const 2))) ::ₘ ProgramEquations.Versions.cite 0 ::ₘ
        ProgramEquations.Versions.ver 0 ::ₘ 0, 1) := by
  obtain ⟨θ, mgu⟩ := ProgramEquationsOpen.exists_isMGU
    (P := [((ProgramRows.Pat.sym 1).at 0, (.const 1 : ProgramRows.Tm))])
    ⟨Mettapedia.Logic.LP.Subst.id _, fun e member => by
      rw [List.mem_singleton] at member
      subst member
      rfl⟩
  exact ProgramNested.CStep.apply 0 ⟨0, by decide⟩ .hole (.const 1) 0 0 0 le_rfl θ mgu

/-! ## The language on the embedding -/

abbrev D : Discipline RSig [] () := ⟨Unit, fun _ _ => True⟩

def supply : ℕ → Term RSig [] () := fun _ => .op (.const 0) .nil

def eqAt : ℕ → ℕ := fun _ => 0

/-- The embedded query `(call k)`. -/
def Q (k : ℕ) : Comp rkeys [] () D.Ty := trEx eqAt [] (.call (.val (.const k)))

/-- The closed numeral `k`. -/
def g (k : ℕ) : Term RSig [] () := .op (.const k) .nil

def sp : Term RSig [] () → Multiset (Row rkeys [] ()) := fun _ => 0
def w0 : World rkeys [] () := ⟨0, 0, sp⟩
def w1 : World rkeys [] () := ⟨1, 0, sp⟩
def w2 : World rkeys [] () := ⟨2, 0, sp⟩

/-- The site of the query's arrow. -/
def s : rkeys.Site := .inr (.inl [0])

/-- The arrow's name, opened at scope `0`; the failing equation's name, copied at scope `1`; the
left-hand side `1`, copied at scope `1`. -/
def Y0 : RData := instantiate (openAt rkeys s 0) (slotD [0])
def Z : RData := instantiate (copyAt rkeys 1) (nameD ⟨[], .var 1 0⟩)
def lhs1 : RData := instantiate (copyAt rkeys 1) (constD 1)

theorem Y0_eq : Y0 = nameD ⟨[0], .slot [0]⟩ := by
  rw [Y0, slotD, instantiate_nameD]
  rfl

theorem Z_eq : Z = nameD ⟨[1], .var 1 0⟩ := by
  rw [Z, instantiate_nameD]
  rfl

def frame0 : Frame rkeys [] () D.Ty := .bindTo s (slotD [0]) (.apply (slotD [0]))

theorem live_nil : Solvable ([] : List (Constraint rkeys [] ())) :=
  ⟨Name rkeys, fam rkeys, fun x => nameD x, fun _ member => by cases member⟩

/-- The solution sending the arrow's name and the failing equation's name to `k`. -/
def solveAt (k : ℕ) : Assignment (fam rkeys) (fam rkeys) := fun x =>
  if x = ⟨[0], .slot [0]⟩ ∨ x = ⟨[1], .var 1 0⟩ then constD k else nameD x

theorem solveAt_Y0 (k : ℕ) : instantiate (solveAt k) Y0 = constD k := by
  rw [Y0_eq, instantiate_nameD]
  exact if_pos (Or.inl rfl)

theorem solveAt_Z (k : ℕ) : instantiate (solveAt k) Z = constD k := by
  rw [Z_eq, instantiate_nameD]
  exact if_pos (Or.inr rfl)

/-- The store after the arrow. -/
def K1 (k : ℕ) : List (Constraint rkeys [] ()) := [(Y0, constD k)]

theorem live_K1 (k : ℕ) : Solvable (K1 k) :=
  ⟨Name rkeys, fam rkeys, solveAt k, fun e member => by
    rw [K1, List.mem_singleton] at member
    subst member
    exact (solveAt_Y0 k).trans rfl⟩

theorem live_failing (k : ℕ) : Solvable (K1 k ++ [(Z, Y0)]) :=
  ⟨Name rkeys, fam rkeys, solveAt k, fun e member => by
    simp only [K1, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (solveAt_Y0 k).trans rfl
    · exact (solveAt_Z k).trans (solveAt_Y0 k).symm⟩

theorem live_matched : Solvable (K1 1 ++ [(lhs1, Y0)]) :=
  ⟨Name rkeys, fam rkeys, solveAt 1, fun e member => by
    simp only [K1, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (solveAt_Y0 1).trans rfl
    · exact (rfl : instantiate (solveAt 1) lhs1 = constD 1).trans (solveAt_Y0 1).symm⟩

theorem dead_mismatch (k : ℕ) (different : k ≠ 1) : ¬ Solvable (K1 k ++ [(lhs1, Y0)]) := by
  rintro ⟨X, target, σ, solved⟩
  have first := solved (Y0, constD k) (by simp [K1])
  have second := solved (lhs1, Y0) (by simp [K1])
  have same := second.trans first
  change (Term.op (Sum.inl (ROp.const 1)) .nil : Term (signature RSig target) [] ()) =
    Term.op (Sum.inl (ROp.const k)) .nil at same
  injection same with _ _ hop _
  simp only [Sum.inl.injEq, ROp.const.injEq] at hop
  exact different hop.symm

/-- **The arrow of the embedded call**: three moves, the same under every program. -/
theorem prefix_runs (Pr : Program rkeys [] () D.Ty) (k : ℕ) :
    Runs D Pr supply (Config.initial (fun _ => 0) (Q k)) ⟨w1, {⟨K1 k, .eval (.apply Y0), [], []⟩}⟩ := by
  refine Relation.ReflTransGen.tail (b := ⟨w0, {⟨[], .value (constD k), [frame0], []⟩}⟩) ?_
    (Step.single live_nil (.letBind w0 [] (constD k) s (slotD [0]) (.apply (slotD [0])) [] []))
  refine Relation.ReflTransGen.tail (b := ⟨w0, {⟨[], .eval (.ret (constD k)), [frame0], []⟩}⟩) ?_
    (Step.single live_nil (.ret w0 [] (constD k) [frame0] []))
  exact Relation.ReflTransGen.single
    (Step.single live_nil (.letStart w0 [] s (slotD [0]) (.ret (constD k)) (.apply (slotD [0])) [] []))

theorem equations_program :
    (program eqs : Program rkeys [] () D.Ty).equations = [trEquation 0 ⟨.sym 1, .val (.sym 2)⟩] := rfl

theorem equations_strict :
    (programStrict eqs : Program rkeys [] () D.Ty).equations =
      [trEquation 0 ⟨.sym 1, .val (.sym 2)⟩, failing 1] := rfl

/-- **The language keeps the call as data**: `(call 5)` has the bag `{5}`, and the run has ended. -/
theorem inert_example :
    ∃ C, Runs D (program eqs) supply (Config.initial (fun _ => 0) (Q 5)) C ∧
      C.Quiescent (program eqs) supply ∧ Config.answers (D := D) C = {{g 5}} := by
  refine ⟨⟨w1, {⟨K1 5, .value Y0, [], []⟩}⟩, ?_, ?_, ?_⟩
  · refine Relation.ReflTransGen.tail (prefix_runs (program eqs) 5)
      (Step.single (live_K1 5) (.unmatched w1 (K1 5) Y0 [] [] fun e member => ?_))
    rw [equations_program, List.mem_singleton] at member
    subst member
    exact dead_mismatch 5 (by decide)
  · intro b member _ w' bs
    rw [Multiset.mem_singleton] at member
    subst member
    exact Move.value_still
  · rw [Config.answers_of_finished ⟨rfl, _, rfl⟩ (live_K1 5)]
    rw [Branch.answer_of_determines (g := g 5) rfl ⟨live_K1 5, fun target σ solved =>
      (solved (Y0, constD 5) (List.mem_singleton.mpr rfl)).trans rfl⟩]

/-- The alternatives the embedded call makes under the program with the failing equation. -/
def callB (k : ℕ) (e : Equation rkeys [] () D.Ty) : Branch rkeys [] () D.Ty := callBranch D 1 (K1 k) Y0 [] [] e

theorem split_strict (k : ℕ) :
    Runs D (programStrict eqs) supply (Config.initial (fun _ => 0) (Q k))
      ⟨w2, {callB k (trEquation 0 ⟨.sym 1, .val (.sym 2)⟩)}⟩ := by
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.tail (prefix_runs (programStrict eqs) k)
      (Step.single (live_K1 k) (.apply w1 (K1 k) Y0 [] [] ⟨failing 1, ?_, live_failing k⟩))) ?_
  · rw [equations_strict]
    simp
  · refine Step.of_eq (b := callB k (failing 1)) (rest := {callB k (trEquation 0 ⟨.sym 1, .val (.sym 2)⟩)})
      ?_ (zero_add _).symm (live_failing k) (.fail w2 (K1 k ++ [(Z, Y0)]) [] [])
    rw [equations_strict]
    exact Multiset.cons_swap (callB k (trEquation 0 ⟨.sym 1, .val (.sym 2)⟩)) (callB k (failing 1)) 0

/-- **With the failing equation, `(call 5)` has no answer**, and the run has ended: its one
alternative is dead. -/
theorem strict_example :
    ∃ C, Runs D (programStrict eqs) supply (Config.initial (fun _ => 0) (Q 5)) C ∧
      C.Quiescent (programStrict eqs) supply ∧ Config.answers (D := D) C = 0 := by
  refine ⟨_, split_strict 5, ?_, Config.answers_of_dead (dead_mismatch 5 (by decide))⟩
  intro b member live
  rw [Multiset.mem_singleton] at member
  subst member
  exact absurd live (dead_mismatch 5 (by decide))

/-- **With the failing equation, `(call 1)` still has the bag `{2}`**, and the run has ended. -/
theorem strict_matched_example :
    ∃ C, Runs D (programStrict eqs) supply (Config.initial (fun _ => 0) (Q 1)) C ∧
      C.Quiescent (programStrict eqs) supply ∧ Config.answers (D := D) C = {{g 2}} := by
  refine ⟨⟨w2, {⟨K1 1 ++ [(lhs1, Y0)], .value (instantiate (copyAt rkeys 1) (constD 2)), [], []⟩}⟩,
    (split_strict 1).tail (Step.single live_matched (.ret w2 _ _ [] [])), ?_, ?_⟩
  · intro b member _ w' bs
    rw [Multiset.mem_singleton] at member
    subst member
    exact Move.value_still
  · rw [Config.answers_of_finished ⟨rfl, _, rfl⟩ live_matched]
    rw [Branch.answer_of_determines (g := g 2) rfl ⟨live_matched, fun _ _ _ => rfl⟩]

#print axioms core_stuck
#print axioms core_matched
#print axioms inert_example
#print axioms strict_example
#print axioms strict_matched_example

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.ExampleStuckCall
