import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionDerivation

/-!
# A complete generator for ground superposition, and the complete given-clause loop

The given-clause loop (`Loop`) is refutationally complete for any sound and complete generator
(`Loop.complete`). This module constructs one.

* **Positions** (`positions`): every context and subterm of a ground term. Every context filling a
  subterm back to the term is listed, up to the argument it overwrites (`exists_position`), and every
  listed one fills back (`fill_of_mem_positions`).
* **Conclusions** (`binaryConclusions`, `unaryConclusions`): for a side and a main premise, every
  superposition conclusion over every side literal, main literal and position; for one premise, every
  equality resolution and equality factoring conclusion.
* **The generator** (`generator`): the unary conclusions of the given clause, and the binary
  conclusions of the given clause with each active clause in both roles and with itself. It is
  **sound** (`generator_sound`) and **complete** (`generator_complete`).
* **The given-clause loop with first-in first-out selection and this generator is refutationally
  complete** (`givenClause_complete`): from an unsatisfiable queue of ground clauses it derives the
  empty clause.

The generator is classical: it lists conclusions by deciding the side conditions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature}

/-! ## Positions -/

/-- **The positions of a ground term**: each context with the subterm at its hole. -/
def positions : GroundTerm sig → List (Ctx sig × GroundTerm sig)
  | .const c => [(.hole, .const c)]
  | .app f args => (.hole, .app f args) :: (List.finRange (sig.functionArity f)).flatMap fun i =>
      (positions (args i)).map fun p => (.app f args i p.1, p.2)

theorem fill_of_mem_positions : ∀ (t : GroundTerm sig) {c : Ctx sig} {u : GroundTerm sig},
    (c, u) ∈ positions t → c.fill u = t
  | .const k, c, u, member => by
      simp only [positions, List.mem_singleton, Prod.mk.injEq] at member
      obtain ⟨rfl, rfl⟩ := member
      rfl
  | .app f args, c, u, member => by
      simp only [positions, List.mem_cons, Prod.mk.injEq, List.mem_flatMap, List.mem_finRange,
        true_and, List.mem_map] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨i, ⟨c', u'⟩, inner, same⟩
      · rfl
      · simp only at same
        obtain ⟨rfl, rfl⟩ := same
        have filled := fill_of_mem_positions (args i) inner
        show GroundTerm.app f (Function.update args i (c'.fill u')) = GroundTerm.app f args
        rw [filled, Function.update_eq_self]

/-- **Every position is listed**, up to the argument the context overwrites. -/
theorem exists_position : ∀ (c : Ctx sig) (u : GroundTerm sig),
    ∃ c' : Ctx sig, (c', u) ∈ positions (c.fill u) ∧ ∀ s, c'.fill s = c.fill s
  | .hole, u => ⟨.hole, by cases u <;> simp [positions, Ctx.fill], fun _ => rfl⟩
  | .app f args i inner, u => by
      obtain ⟨c', member, same⟩ := exists_position inner u
      refine ⟨.app f (Function.update args i (inner.fill u)) i c', ?_, fun s => ?_⟩
      · show (_, u) ∈ positions (GroundTerm.app f (Function.update args i (inner.fill u)))
        simp only [positions, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
        refine Or.inr ⟨i, (c', u), ?_, rfl⟩
        rw [Function.update_self]
        exact member
      · show GroundTerm.app f (Function.update (Function.update args i (inner.fill u)) i (c'.fill s)) =
          GroundTerm.app f (Function.update args i (inner.fill s))
        rw [Function.update_idem, same]

/-! ## Conclusions -/

section Conclusions

variable [LinearOrder (GroundTerm sig)]

/-- The main-literal side conditions of superposition: maximal when negative, strictly maximal and
above the side literal when positive. -/
def MainOK (C : Clause (GroundTerm sig)) (L S : Lit (GroundTerm sig)) : Prop :=
  (L.negative = true → ∀ M ∈ C.erase L, M ≤ L) ∧ (L.negative = false → (∀ M ∈ C.erase L, M < L) ∧ S < L)

open Classical in
/-- **The superposition conclusions** of a side premise `D` into a main premise `C`: over every side
literal, every main literal and every position of its larger side. -/
noncomputable def binaryConclusions (D C : Clause (GroundTerm sig)) : List (Clause (GroundTerm sig)) :=
  D.toList.flatMap fun S => C.toList.flatMap fun L => (positions L.lhs).filterMap fun p =>
    if S.negative = false ∧ S.rhs < S.lhs ∧ (∀ M ∈ D.erase S, M < S) ∧ p.2 = S.lhs ∧
        L.rhs < L.lhs ∧ MainOK C L S then
      some (Lit.make L.negative (p.1.fill S.rhs) L.rhs ::ₘ (D.erase S + C.erase L))
    else none

open Classical in
/-- **The equality resolution and equality factoring conclusions** of one premise. -/
noncomputable def unaryConclusions (C : Clause (GroundTerm sig)) : List (Clause (GroundTerm sig)) :=
  C.toList.flatMap fun L =>
    (if L.negative = true ∧ L.rhs = L.lhs ∧ (∀ M ∈ C.erase L, M ≤ L) then [C.erase L] else []) ++
    (C.erase L).toList.flatMap fun L' =>
      if L.negative = false ∧ L'.negative = false ∧ L'.lhs = L.lhs ∧ L.rhs < L.lhs ∧
          (∀ M ∈ C.erase L, M ≤ L) then
        [Lit.make true L.rhs L'.rhs ::ₘ C.erase L]
      else []

/-- **The generator**: the unary conclusions of the given clause, and the superposition conclusions
of the given clause with itself and with each active clause, in both roles. -/
noncomputable def generator : Generator sig := fun given active =>
  unaryConclusions given ++ (given :: active).flatMap (fun D => binaryConclusions D given) ++
    active.flatMap fun C => binaryConclusions given C

/-- A side literal of a premise is the positive literal it names. -/
theorem pos_of_positive {S : Lit (GroundTerm sig)} (positive : S.negative = false) :
    S = Lit.pos S.lhs S.rhs S.oriented :=
  Lit.ext rfl positive rfl

/-- **Every listed superposition conclusion is the conclusion of an inference.** -/
theorem inference_of_mem_binary {D C E : Clause (GroundTerm sig)} (member : E ∈ binaryConclusions D C) :
    Inference (some D) C E := by
  classical
  simp only [binaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_filterMap] at member
  obtain ⟨S, inD, L, inC, ⟨c, u⟩, position, produced⟩ := member
  split_ifs at produced with conditions
  obtain ⟨positive, decreasing, sideMax, atL, strict, mainMax⟩ := conditions
  simp only [Option.some.injEq] at produced
  subst produced
  have filled : c.fill S.lhs = L.lhs := by
    rw [← atL]
    exact fill_of_mem_positions _ position
  have side : Lit.pos S.lhs S.rhs decreasing.le ::ₘ D.erase S = D := by
    rw [← pos_of_positive positive]
    exact Multiset.cons_erase inD
  have main : L ::ₘ C.erase L = C := Multiset.cons_erase inC
  have sideMax' : ∀ M ∈ D.erase S, M < Lit.pos S.lhs S.rhs decreasing.le := by
    rw [← pos_of_positive positive]
    exact sideMax
  rcases Bool.eq_false_or_eq_true L.negative with sign | sign
  · have inference := Inference.negSup (D.erase S) (C.erase L) L c decreasing sideMax' sign filled.symm
      strict (mainMax.1 sign)
    rw [side, main] at inference
    rwa [sign]
  · have smaller : Lit.pos S.lhs S.rhs decreasing.le < L := by
      rw [← pos_of_positive positive]
      exact (mainMax.2 sign).2
    have inference := Inference.posSup (D.erase S) (C.erase L) L c decreasing sideMax' sign filled.symm
      strict (mainMax.2 sign).1 smaller
    rw [side, main] at inference
    rwa [sign]

/-- **Every listed unary conclusion is the conclusion of an inference.** -/
theorem inference_of_mem_unary {C E : Clause (GroundTerm sig)} (member : E ∈ unaryConclusions C) :
    Inference none C E := by
  classical
  simp only [unaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_append] at member
  obtain ⟨L, inC, resolved | factored⟩ := member
  · split_ifs at resolved with conditions
    · rw [List.mem_singleton] at resolved
      subst resolved
      obtain ⟨negative, trivial, mainMax⟩ := conditions
      have inference := Inference.eqRes (C.erase L) L negative trivial mainMax
      rwa [Multiset.cons_erase inC] at inference
    · simp at resolved
  · obtain ⟨L', inRest, produced⟩ := factored
    split_ifs at produced with conditions
    · rw [List.mem_singleton] at produced
      subst produced
      obtain ⟨positive, positive', same, strict, mainMax⟩ := conditions
      have rest : L' ::ₘ (C.erase L).erase L' = C.erase L := Multiset.cons_erase inRest
      have inference := Inference.eqFact ((C.erase L).erase L') L L' positive positive' same strict
        (by rw [rest]; exact mainMax)
      rw [rest, Multiset.cons_erase inC] at inference
      exact inference
    · simp at produced

/-- **Every inference with side premise `D` and main premise `C` is listed.** -/
theorem mem_binary_of_inference {D C E : Clause (GroundTerm sig)} (inference : Inference (some D) C E) :
    E ∈ binaryConclusions D C := by
  classical
  generalize hside : (some D : Option (Clause (GroundTerm sig))) = side at inference
  cases inference with
  | @posSup l r D₀ C₀ L c decreasing sideMax positive larger strict mainMax smaller =>
      simp only [Option.some.injEq] at hside
      subst hside
      obtain ⟨c', listed, same⟩ := exists_position c l
      simp only [binaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_filterMap]
      refine ⟨Lit.pos l r decreasing.le, Multiset.mem_cons_self _ _, L, Multiset.mem_cons_self _ _,
        (c', l), larger ▸ listed, ?_⟩
      rw [Multiset.erase_cons_head, Multiset.erase_cons_head, if_pos ⟨rfl, decreasing, sideMax, rfl,
        strict, fun h => absurd (h.symm.trans positive) (by decide), fun _ => ⟨by rw [Multiset.erase_cons_head]; exact mainMax, smaller⟩⟩]
      show some (Lit.make L.negative (c'.fill r) L.rhs ::ₘ (D₀ + C₀)) = some _
      rw [same, positive]
  | @negSup l r D₀ C₀ L c decreasing sideMax negative larger strict mainMax =>
      simp only [Option.some.injEq] at hside
      subst hside
      obtain ⟨c', listed, same⟩ := exists_position c l
      simp only [binaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_filterMap]
      refine ⟨Lit.pos l r decreasing.le, Multiset.mem_cons_self _ _, L, Multiset.mem_cons_self _ _,
        (c', l), larger ▸ listed, ?_⟩
      rw [Multiset.erase_cons_head, Multiset.erase_cons_head, if_pos ⟨rfl, decreasing, sideMax, rfl,
        strict, fun _ => by rw [Multiset.erase_cons_head]; exact mainMax, fun h => absurd (negative.symm.trans h) (by decide)⟩]
      show some (Lit.make L.negative (c'.fill r) L.rhs ::ₘ (D₀ + C₀)) = some _
      rw [same, negative]
  | eqRes C₀ L negative trivial mainMax => exact absurd hside (by simp)
  | eqFact C₀ L L' positive positive' same strict mainMax => exact absurd hside (by simp)

/-- **Every inference with one premise is listed.** -/
theorem mem_unary_of_inference {C E : Clause (GroundTerm sig)} (inference : Inference none C E) :
    E ∈ unaryConclusions C := by
  classical
  generalize hside : (none : Option (Clause (GroundTerm sig))) = side at inference
  cases inference with
  | posSup => exact absurd hside (by simp)
  | negSup => exact absurd hside (by simp)
  | eqRes C₀ L negative trivial mainMax =>
      simp only [unaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_append]
      refine ⟨L, Multiset.mem_cons_self _ _, Or.inl ?_⟩
      rw [Multiset.erase_cons_head, if_pos ⟨negative, trivial, mainMax⟩]
      exact List.mem_singleton.mpr rfl
  | eqFact C₀ L L' positive positive' same strict mainMax =>
      simp only [unaryConclusions, List.mem_flatMap, Multiset.mem_toList, List.mem_append]
      refine ⟨L, Multiset.mem_cons_self _ _, Or.inr ⟨L', ?_, ?_⟩⟩
      · rw [Multiset.erase_cons_head]
        exact Multiset.mem_cons_self _ _
      · rw [Multiset.erase_cons_head, if_pos ⟨positive, positive', same, strict, mainMax⟩]
        exact List.mem_singleton.mpr rfl

/-- **The generator is sound.** -/
theorem generator_sound : Generator.Sound (generator (sig := sig)) := by
  intro given active concl member I holds
  simp only [generator, List.mem_append, List.mem_flatMap, List.mem_cons] at member
  rcases member with (unary | ⟨D, inD, binary⟩) | ⟨C, inC, binary⟩
  · exact (inference_of_mem_unary unary).sound I (fun _ member => by cases member)
      (holds given (Or.inl rfl))
  · refine (inference_of_mem_binary binary).sound I (fun X member => ?_) (holds given (Or.inl rfl))
    rw [Option.mem_def, Option.some.injEq] at member
    subst member
    rcases inD with rfl | inActive
    · exact holds _ (Or.inl rfl)
    · exact holds _ (Or.inr inActive)
  · refine (inference_of_mem_binary binary).sound I (fun X member => ?_) (holds C (Or.inr inC))
    rw [Option.mem_def, Option.some.injEq] at member
    subst member
    exact holds _ (Or.inl rfl)

/-- **The generator is complete.** -/
theorem generator_complete : Generator.Complete (generator (sig := sig)) := by
  intro given active side main concl inference sides mainIn involved
  simp only [generator, List.mem_append, List.mem_flatMap, List.mem_cons]
  cases side with
  | none =>
      have isGiven : main = given := by
        rcases involved with same | inSide
        · exact same
        · cases inSide
      subst isGiven
      exact Or.inl (Or.inl (mem_unary_of_inference inference))
  | some D =>
      rcases involved with rfl | inSide
      · rcases sides D rfl with rfl | inActive
        · exact Or.inl (Or.inr ⟨_, Or.inl rfl, mem_binary_of_inference inference⟩)
        · exact Or.inl (Or.inr ⟨D, Or.inr inActive, mem_binary_of_inference inference⟩)
      · rw [Option.mem_def, Option.some.injEq] at inSide
        subst inSide
        rcases mainIn with rfl | inActive
        · exact Or.inl (Or.inr ⟨_, Or.inl rfl, mem_binary_of_inference inference⟩)
        · exact Or.inr ⟨main, inActive, mem_binary_of_inference inference⟩

variable [WellFoundedLT (GroundTerm sig)]

/-- **The given-clause loop is refutationally complete**: with first-in first-out selection and the
generator, from an unsatisfiable queue of ground clauses and no active clauses, it derives the empty
clause. -/
theorem givenClause_complete [GroundSimplification sig] (passive : List (Clause (GroundTerm sig)))
    (unsatisfiable : ¬ ∃ I : Congruence sig, ∀ C ∈ passive, Models I.rel C) :
    ∃ i, (0 : Clause (GroundTerm sig)) ∈ Loop.clauses (Loop.run generator ⟨[], passive⟩ i) :=
  Loop.complete generator generator_sound generator_complete ⟨[], passive⟩ rfl unsatisfiable

omit [WellFoundedLT (GroundTerm sig)] in
/-- **Every clause the loop derives follows from the initial queue.** -/
theorem givenClause_sound (passive : List (Clause (GroundTerm sig))) (i : ℕ)
    {C : Clause (GroundTerm sig)} (member : C ∈ Loop.clauses (Loop.run generator ⟨[], passive⟩ i)) :
    Entails {D | D ∈ passive} C := by
  have entails := (Loop.derivation generator generator_sound ⟨[], passive⟩).entails i member
  refine entails.mono fun D member => ?_
  rcases member with active | queued
  · cases active
  · exact queued

end Conclusions

#print axioms fill_of_mem_positions
#print axioms exists_position
#print axioms inference_of_mem_binary
#print axioms inference_of_mem_unary
#print axioms mem_binary_of_inference
#print axioms mem_unary_of_inference
#print axioms generator_sound
#print axioms generator_complete
#print axioms givenClause_complete
#print axioms givenClause_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
