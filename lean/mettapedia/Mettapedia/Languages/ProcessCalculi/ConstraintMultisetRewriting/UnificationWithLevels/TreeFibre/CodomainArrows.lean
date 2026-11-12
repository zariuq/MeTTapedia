import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainDecompose

/-!
# Equations between arrow codes with codomains, decided

A solver of the tree's driver (`arrowCodSolver`) on stores of equations between arrow codes with codomains at
universes. On the first equation it

* deletes it when its two sides have one code;
* when a side is an unknown `X`, refutes by the full occurs check or by a misfit head, or narrows the misfit unknowns to
  greatest lower bounds and solves `X := t` (`codNarrowSolveUpdate`), in either orientation;
* when both sides are rigid, removes equal heads, decomposes two Π types into their domains and their codomains
  (`decomposeCodUpdate`), and refutes every clash.

Its rank is the number of unknowns occurring in the store, then the number of nodes of its sides: solving removes an
unknown from the store, every other step removes nodes.

**The fragment** (`InArrowsCod`): every equation is between two arrow codes with codomains at a universe
(`ArrowCodEq`); the unknowns met are declared at universes and no declaration mentions them, the rest of the telescope
arbitrary; the heads of the sides have computed types. The declared universes need not be comparable: narrowing goes
to greatest lower bounds. It contains the fragment of first-order arrow codes, without
its chain of declarations (`inArrowsCod_of_arrows`), and the flex–rigid fragment with codomains
(`inArrowsCod_of_flexCod`).

* Kept by every progress (`arrowCodRound_stable`); **progress by shape** (`arrowCodRound_ne_stuck`), for a total
  greatest lower bound; **decided** (`arrowsCod_decided`): at some budget and every larger one, a principal answer or a
  certified refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentOccursCheck (nodes)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Heads of arrow codes with codomains -/

section Support

/-- The heads of a Π code with codomains: those of the domain and those of the codomain. -/
theorem mem_codHeads_pi {n : Nat} {A B : Tm Head n} {h : Head} :
    h ∈ codHeads (Tm.pi A (Presentation.rename wk B)) ↔ h ∈ codHeads A ∨ h ∈ codHeads B := by
  change h ∈ codHeads A ++ codHeads (Presentation.rename wk B) ↔ _
  rw [codHeads_rename, List.mem_append]

end Support

/-! ## The rank -/

section Rank

/-- An unknown occurs in a side of a store. -/
def occursCod {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) (i : Fin Γ.arity) : Bool :=
  problem.any fun e => decide (i ∈ e.1.2.code.support) || decide (i ∈ e.2.2.code.support)

/-- **The rank**: the number of unknowns occurring in the store, then its size. -/
def codRank {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Nat × Nat :=
  (((List.finRange Γ.arity).filter (occursCod problem)).length, storeSize problem)

theorem occursCod_cons {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ))
    (i : Fin Γ.arity) :
    occursCod (e :: rest) i = true ↔
      (i ∈ e.1.2.code.support ∨ i ∈ e.2.2.code.support) ∨ occursCod rest i = true := by
  simp only [occursCod, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]

/-- **Removing the first equation lowers the rank.** -/
theorem codRank_drop {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ)) :
    ContextualDependentWorklist.Below (codRank rest) (codRank (e :: rest)) := by
  refine below_of_le_lt (filter_length_le _ fun i _ h => (occursCod_cons e rest i).mpr (.inr h)) ?_
  have := nodes_pos e.1.2.code
  simp only [storeSize]
  omega

/-- **Swapping the sides of the first equation keeps the rank.** -/
theorem codRank_swap {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ)) :
    codRank (((e.2, e.1) : Equation (TotalTerm Γ)) :: rest) = codRank (e :: rest) := by
  have occ : occursCod (((e.2, e.1) : Equation (TotalTerm Γ)) :: rest) = occursCod (e :: rest) := by
    funext i
    simp only [occursCod, List.any_cons, Bool.or_comm]
  unfold codRank
  rw [occ]
  simp only [storeSize]
  congr 1
  omega

/-- **Decomposition lowers the rank**: the unknowns of the parts are those of the whole, and the parts are smaller. -/
theorem codRank_decompose {Θ : Context S.R} {e d c : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) (dl : d.1.2.code = A) (dr : d.2.2.code = A')
    (cl : c.1.2.code = B) (cr : c.2.2.code = B') :
    ContextualDependentWorklist.Below (codRank (d :: c :: rest)) (codRank (e :: rest)) := by
  refine below_of_le_lt (filter_length_le _ fun i _ inside => ?_) ?_
  · rcases (occursCod_cons _ _ i).mp inside with hit | hit
    · apply (occursCod_cons e rest i).mpr
      left
      rw [left, right, mem_support_pi_wk, mem_support_pi_wk]
      rw [dl, dr] at hit
      rcases hit with h | h
      · exact .inl (.inl h)
      · exact .inr (.inl h)
    · rcases (occursCod_cons _ _ i).mp hit with hit | hit
      · apply (occursCod_cons e rest i).mpr
        left
        rw [left, right, mem_support_pi_wk, mem_support_pi_wk]
        rw [cl, cr] at hit
        rcases hit with h | h
        · exact .inl (.inr h)
        · exact .inr (.inr h)
      · exact (occursCod_cons e rest i).mpr (.inr hit)
  · simp only [storeSize]
    rw [left, right, dl, dr, cl, cr]
    simp only [nodes, ContextualDependentOccursFull.nodes_rename]
    omega

/-- Every side of the store is an arrow code with codomains. -/
def AllArrowCod {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ e ∈ problem, ArrowCod e.1.2.code ∧ ArrowCod e.2.2.code

/-- Whether every side of the store is an arrow code with codomains, decided. -/
def allArrowCodB {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Bool :=
  problem.all fun e => arrowCodB e.1.2.code && arrowCodB e.2.2.code

theorem allArrowCod_of_B {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (h : allArrowCodB problem = true) : AllArrowCod problem := by
  intro e member
  have he := List.all_eq_true.mp h e member
  simp only [Bool.and_eq_true] at he
  exact ⟨arrowCod_of_B _ _ le_rfl he.1, arrowCod_of_B _ _ le_rfl he.2⟩

theorem allArrowCodB_of {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (h : AllArrowCod problem) :
    allArrowCodB problem = true := by
  apply List.all_eq_true.mpr
  intro e member
  simp only [Bool.and_eq_true]
  exact ⟨arrowCodB_of_arrowCod (h e member).1, arrowCodB_of_arrowCod (h e member).2⟩

end Rank

/-! ## Solving lowers the rank -/

section SolveRank

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

/-- **After narrowing and solving, the unknowns occurring are among those before, without the solved one.** -/
theorem occursCod_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (ok : CodSolvable glb v)
    {rest : EquationStore (TotalTerm Θ)} (codes : AllArrowCod rest) (i : Fin Θ.arity)
    (after : occursCod ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) i = true) :
    occursCod (e :: rest) i = true ∧ i ≠ v.X := by
  simp only [occursCod, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at after
  obtain ⟨e'', member, hit⟩ := after
  obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
  obtain ⟨codeL, codeR⟩ := codes e' inRest
  have sides : ∀ (c : Tm Head Θ.arity), ArrowCod c →
      i ∈ (Presentation.subst (solveSub v.X e.2.2.code) c).support →
        (i ∈ c.support ∧ i ≠ v.X) ∨ i ∈ e.2.2.code.support := fun c code inside =>
    support_subst_solve code i inside
  have inside : (i ∈ e'.1.2.code.support ∧ i ≠ v.X) ∨ (i ∈ e'.2.2.code.support ∧ i ≠ v.X) ∨
      i ∈ e.2.2.code.support := by
    rcases hit with hitL | hitR
    · rcases sides _ codeL hitL with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rcases sides _ codeR hitR with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  rcases inside with ⟨h, ne⟩ | ⟨h, ne⟩ | h
  · refine ⟨(occursCod_cons e rest i).mpr (.inr ?_), ne⟩
    simp only [occursCod, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨e', inRest, .inl h⟩
  · refine ⟨(occursCod_cons e rest i).mpr (.inr ?_), ne⟩
    simp only [occursCod, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨e', inRest, .inr h⟩
  · exact ⟨(occursCod_cons e rest i).mpr (.inl (.inr h)), fun same => ok.absent (same ▸ h)⟩

/-- **Narrowing and solving lowers the rank.** -/
theorem codRank_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (ok : CodSolvable glb v)
    {rest : EquationStore (TotalTerm Θ)} (codes : AllArrowCod rest) :
    ContextualDependentWorklist.Below
      (codRank ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest)) (codRank (e :: rest)) := by
  apply Prod.Lex.left
  apply filter_length_lt (List.finRange Θ.arity)
    (fun i _ h => (occursCod_solved glb spec algebra v ok codes i h).1) v.X (List.mem_finRange v.X)
  · apply (occursCod_cons e rest v.X).mpr
    left
    left
    rw [v.side_left]
    exact Finset.mem_singleton_self _
  · cases h : occursCod ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) v.X with
    | false => rfl
    | true => exact absurd rfl (occursCod_solved glb spec algebra v ok codes v.X h).2

end SolveRank

/-! ## The fragment -/

section Fragment

/-- **The fragment of equations between arrow codes with codomains**: the unknowns of the sides declared at universes,
no declaration mentioning an unknown of the store. -/
structure InArrowsCod (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  occurring : ∀ e ∈ problem, AtUniverses (S := S) Θ.raw e.1.2.code ∧ AtUniverses (S := S) Θ.raw e.2.2.code
  apart : ∀ e ∈ problem, SidesApart Θ.raw e.1.2.code e.2.2.code
  shapes : ∀ e ∈ problem, Nonempty (ArrowCodEq e)
  typedHeads : ∀ e ∈ problem, (∀ h ∈ codHeads e.1.2.code, (choices.typing h).isSome = true) ∧
    (∀ h ∈ codHeads e.2.2.code, (choices.typing h).isSome = true)

theorem InArrowsCod.codes {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InArrowsCod choices problem) : AllArrowCod problem := by
  intro e member
  obtain ⟨w⟩ := inside.shapes e member
  exact ⟨w.code_left, w.code_right⟩

theorem inArrowsCod_drop {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrowsCod choices (e :: rest)) :
    InArrowsCod choices rest :=
  ⟨fun e' member => inside.occurring e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.apart e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.typedHeads e' (List.mem_cons_of_mem _ member)⟩

theorem inArrowsCod_swap {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrowsCod choices (e :: rest)) :
    InArrowsCod choices (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) := by
  refine ⟨fun e' member => ?_, fun e' member => ?_, fun e' member => ?_, fun e' member => ?_⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨(inside.occurring e List.mem_cons_self).2, (inside.occurring e List.mem_cons_self).1⟩
    · exact inside.occurring e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact (inside.apart e List.mem_cons_self).swap
    · exact inside.apart e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨w⟩ := inside.shapes e List.mem_cons_self
      exact ⟨w.swap⟩
    · exact inside.shapes e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨(inside.typedHeads e List.mem_cons_self).2, (inside.typedHeads e List.mem_cons_self).1⟩
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ member)

/-- **The fragment of first-order arrow codes lies inside**, without its chain of declarations. -/
theorem inArrowsCod_of_arrows {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InArrows choices problem) : InArrowsCod choices problem := by
  refine ⟨fun _ _ => ⟨fun Y _ => inside.universes Y, fun Y _ => inside.universes Y⟩,
    fun _ _ => sidesApart_of_universes inside.universes _ _, fun e member => ?_, fun e member => ?_⟩
  · obtain ⟨w⟩ := inside.shapes e member
    exact ⟨w.toCod⟩
  · obtain ⟨w⟩ := inside.shapes e member
    obtain ⟨headsL, headsR⟩ := inside.typedHeads e member
    exact ⟨fun h hh => headsL h (mem_codHeads_of_arrow w.arrow_left h hh),
      fun h hh => headsR h (mem_codHeads_of_arrow w.arrow_right h hh)⟩

/-- **The flex–rigid fragment with codomains lies inside.** -/
theorem inArrowsCod_of_flexCod {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InFlexCod choices problem) : InArrowsCod choices problem := by
  refine ⟨fun e member => ⟨?_, inside.occurring e member⟩, inside.apart, fun e member => ?_, fun e member => ?_⟩
  · obtain ⟨v⟩ := inside.shapes e member
    intro Y inY
    rw [v.side_left] at inY
    rw [Finset.mem_singleton.mp inY]
    exact ⟨v.u, v.declared, v.universe_u⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact ⟨⟨v.v, v.annotation_left, v.annotation_right, v.universe_v, by rw [v.side_left]; exact .var v.X, v.code⟩⟩
  · obtain ⟨v⟩ := inside.shapes e member
    refine ⟨fun h hh => ?_, inside.typedHeads e member⟩
    rw [v.side_left] at hh
    cases hh

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

/-- **Narrowing and solving keeps the fragment.** -/
theorem inArrowsCod_solved {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrowsCod choices (e :: rest))
    (v : FlexCod e) (ok : CodSolvable glb v) :
    InArrowsCod choices ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) := by
  have occT : AtUniverses (S := S) Θ.raw e.2.2.code := (inside.occurring e List.mem_cons_self).2
  have apartE : SidesApart Θ.raw e.1.2.code e.2.2.code := inside.apart e List.mem_cons_self
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    have occ := inside.occurring e' (List.mem_cons_of_mem _ inRest)
    exact ⟨atUniverses_solved glb spec v w.code_left occ.1 occT, atUniverses_solved glb spec v w.code_right occ.2 occT⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    exact sidesApart_solved glb spec v w.code_left w.code_right (inside.apart e' (List.mem_cons_of_mem _ inRest))
      apartE
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    exact ⟨{
      v := w.v
      annotation_left := by
        change Presentation.subst (solveSub v.X e.2.2.code) e'.1.1.code = .head w.v
        rw [w.annotation_left]
        rfl
      annotation_right := by
        change Presentation.subst (solveSub v.X e.2.2.code) e'.2.1.code = .head w.v
        rw [w.annotation_right]
        rfl
      universe_v := w.universe_v
      code_left := arrowCod_subst_solve v.code w.code_left
      code_right := arrowCod_subst_solve v.code w.code_right }⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    have heads' := inside.typedHeads e' (List.mem_cons_of_mem _ inRest)
    have headsE := (inside.typedHeads e List.mem_cons_self).2
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · rcases codHeads_subst_solve w.code_left h hh with inner | fromT
      · exact heads'.1 h inner
      · exact headsE h fromT
    · rcases codHeads_subst_solve w.code_right h hh with inner | fromT
      · exact heads'.2 h inner
      · exact headsE h fromT

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

omit [DecidableRel S.R.cumulative] in
/-- **Decomposition keeps the fragment.** -/
theorem inArrowsCod_decompose {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrowsCod choices (e :: rest))
    (w : ArrowCodEq e) {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) :
    InArrowsCod choices
      (domainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right ::
        codomainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right :: rest) := by
  have codeL : ArrowCod (Tm.pi A (Presentation.rename wk B)) := left ▸ w.code_left
  have codeR : ArrowCod (Tm.pi A' (Presentation.rename wk B')) := right ▸ w.code_right
  obtain ⟨cA, cB⟩ := arrowCod_pi_parts codeL
  obtain ⟨cA', cB'⟩ := arrowCod_pi_parts codeR
  obtain ⟨headsL, headsR⟩ := inside.typedHeads e List.mem_cons_self
  rw [left] at headsL
  rw [right] at headsR
  obtain ⟨occL, occR⟩ := inside.occurring e List.mem_cons_self
  rw [left] at occL
  rw [right] at occR
  have apartE := inside.apart e List.mem_cons_self
  rw [left, right] at apartE
  refine ⟨fun e' member => ?_, fun e' member => ?_, fun e' member => ?_, fun e' member => ?_⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun Y h => occL Y (mem_support_pi_wk.mpr (.inl h)), fun Y h => occR Y (mem_support_pi_wk.mpr (.inl h))⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun Y h => occL Y (mem_support_pi_wk.mpr (.inr h)), fun Y h => occR Y (mem_support_pi_wk.mpr (.inr h))⟩
    · exact inside.occurring e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact fun i j hj => ⟨fun h => (apartE i j hj).1 (mem_support_pi_wk.mpr (.inl h)),
        fun h => (apartE i j hj).2 (mem_support_pi_wk.mpr (.inl h))⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact fun i j hj => ⟨fun h => (apartE i j hj).1 (mem_support_pi_wk.mpr (.inr h)),
        fun h => (apartE i j hj).2 (mem_support_pi_wk.mpr (.inr h))⟩
    · exact inside.apart e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨w.v, w.annotation_left, w.annotation_left, w.universe_v, cA, cA'⟩⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨w.v, w.annotation_left, w.annotation_left, w.universe_v, cB, cB'⟩⟩
    · exact inside.shapes e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun h hh => headsL h (mem_codHeads_pi.mpr (.inl hh)),
        fun h hh => headsR h (mem_codHeads_pi.mpr (.inl hh))⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun h hh => headsL h (mem_codHeads_pi.mpr (.inr hh)),
        fun h hh => headsR h (mem_codHeads_pi.mpr (.inr hh))⟩
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ member)

end Fragment

/-! ## The solver -/

section Solver

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)
  (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)

/-- The view of an equation whose left side is an unknown declared at a universe. -/
def flexLeftCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {X : Fin Θ.arity} {u : Head}
    (hX : varOf e.1.2.code = some X) (hu : declaredUniverse Θ.raw X = some u) (huu : S.R.isUniverse u) :
    FlexCod e :=
  ⟨w.v, X, u, w.annotation_left, w.annotation_right, varOf_sound hX, headOf_sound hu, huu, w.universe_v,
    w.code_right⟩

/-- **The step on an equation with an unknown on the left**: the full occurs check, a misfit head, or narrowing to
greatest lower bounds and solving. -/
def flexStepCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (ne : e.2.2.code ≠ .var v.X)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels codRank (e :: rest) :=
  if hocc : v.X ∈ e.2.2.code.support then
    .refuted (cod_occurs_refutes facts roots heads algebra rigid complete v hocc ne rest)
  else match hmis : (codHeads e.2.2.code).find? (misfitPred choices v.u) with
    | some _ =>
        .refuted (cod_misfitHead_refutes facts roots heads algebra rigid complete v (List.mem_of_find?_eq_some hmis)
          (misfit_apart choices headTypingUnique (List.find?_some hmis)) rest)
    | none =>
        if hok : codSolvableB choices glb v = true ∧ allArrowCodB rest = true then
          .progress (codNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v
              (codSolvable_of_B choices glb v hok.1 hocc) rest)
            (codRank_solved glb spec algebra v (codSolvable_of_B choices glb v hok.1 hocc) (allArrowCod_of_B hok.2))
        else .stuck

/-- A round on the swapped equation, read on the equation. -/
def swapRoundCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} :
    Round S.levels codRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) → Round S.levels codRank (e :: rest)
  | .progress update smaller =>
      .progress (update.rephrase (swap_equivalent e rest)) (by
        have same := codRank_swap e rest
        change ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))
        rw [← same]
        exact smaller)
  | .refuted absent =>
      .refuted (fun ⟨Δ, σ, models⟩ => absent ⟨Δ, σ, (swap_equivalent e rest Δ σ).mp models⟩)
  | .stuck => .stuck

/-- **The step on two rigid sides**: equal heads, decomposition into domains and codomains, or a clash. -/
def rigidStepCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels codRank (e :: rest) :=
  match hl : rigidCodOf e.1.2.code, hr : rigidCodOf e.2.2.code with
  | some (.head h), some (.head h') =>
      if same : h = h' then
        .progress (deleteCodes e (w.annotation_left.trans w.annotation_right.symm)
            (by rw [rigidCodOf_head hl, rigidCodOf_head hr, same]) rest)
          (codRank_drop e rest)
      else if equal : S.R.headEq h h' then
        .progress (headEqUpdate facts algebra (arrowEqOfHeads w (rigidCodOf_head hl) (rigidCodOf_head hr))
            (rigidCodOf_head hl) (rigidCodOf_head hr) equal rest) (codRank_drop e rest)
      else .refuted (headClash_refutes facts (arrowEqOfHeads w (rigidCodOf_head hl) (rigidCodOf_head hr))
        (rigidCodOf_head hl) (rigidCodOf_head hr) (fun hs => by rcases hs with h₁ | h₂ <;> contradiction) rest)
  | some (.head _), some (.pi _ _) =>
      .refuted (headPiCod_refutes facts w (rigidCodOf_head hl) (rigidCodOf_pi hr) rest)
  | some (.pi _ _), some (.head _) =>
      .refuted (piHeadCod_refutes facts w (rigidCodOf_pi hl) (rigidCodOf_head hr) rest)
  | some (.pi A B), some (.pi A' B') =>
      .progress (decomposeCodUpdate facts roots heads algebra rigid complete headTypingUnique declared strengthening w
          (rigidCodOf_pi hl) (rigidCodOf_pi hr) rest)
        (codRank_decompose (rigidCodOf_pi hl) (rigidCodOf_pi hr) rfl rfl rfl rfl)
  | none, _ => .stuck
  | some _, none => .stuck

/-- **One step on a read equation.** -/
def stepArrowCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels codRank (e :: rest) :=
  if hsame : e.1.2.code = e.2.2.code then
    .progress (deleteCodes e (w.annotation_left.trans w.annotation_right.symm) hsame rest) (codRank_drop e rest)
  else match hX : varOf e.1.2.code with
    | some X =>
        match hu : declaredUniverse Θ.raw X with
        | some u =>
            if huu : S.R.isUniverse u then
              flexStepCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
                (flexLeftCod w hX hu huu) (fun same => hsame ((varOf_sound hX).trans same.symm)) rest
            else .stuck
        | none => .stuck
    | none =>
        match hY : varOf e.2.2.code with
        | some Y =>
            match hu : declaredUniverse Θ.raw Y with
            | some u =>
                if huu : S.R.isUniverse u then
                  swapRoundCod (flexStepCod choices glb spec facts roots heads algebra rigid complete headTypingUnique
                    declared (flexLeftCod w.swap hY hu huu)
                    (fun same => hsame ((varOf_sound hY).trans same.symm).symm) rest)
                else .stuck
            | none => .stuck
        | none => rigidStepCod facts roots heads algebra rigid complete headTypingUnique declared strengthening w rest

/-- **Read an equation between two arrow codes with codomains at a universe** off its codes. -/
def readArrowCodEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option Head :=
  (headOf e.1.1.code).bind fun v =>
    if e.2.1.code = .head v ∧ S.R.isUniverse v ∧ arrowCodB e.1.2.code = true ∧ arrowCodB e.2.2.code = true then
      some v
    else none

omit [DecidableRel S.R.cumulative] [DecidableRel S.R.headEq] in
theorem readArrowCodEq_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {v : Head}
    (h : readArrowCodEq e = some v) :
    e.1.1.code = .head v ∧ e.2.1.code = .head v ∧ S.R.isUniverse v ∧ ArrowCod e.1.2.code ∧ ArrowCod e.2.2.code := by
  unfold readArrowCodEq at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨v', hv, h⟩ := h
  split_ifs at h with hc
  cases h
  exact ⟨headOf_sound hv, hc.1, hc.2.1, arrowCod_of_B _ _ le_rfl hc.2.2.1, arrowCod_of_B _ _ le_rfl hc.2.2.2⟩

/-- The view of a successful reading. -/
def viewOfArrowCodEq {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {v : Head} (h : readArrowCodEq e = some v) :
    ArrowCodEq e :=
  ⟨v, (readArrowCodEq_sound h).1, (readArrowCodEq_sound h).2.1, (readArrowCodEq_sound h).2.2.1,
    (readArrowCodEq_sound h).2.2.2.1, (readArrowCodEq_sound h).2.2.2.2⟩

omit [DecidableRel S.R.cumulative] [DecidableRel S.R.headEq] in
theorem readArrowCodEq_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) :
    readArrowCodEq e = some w.v := by
  unfold readArrowCodEq
  rw [w.annotation_left]
  simp [headOf, w.annotation_right, w.universe_v, arrowCodB_of_arrowCod w.code_left,
    arrowCodB_of_arrowCod w.code_right]

/-- **The round of the solver**: read the first equation, then step. -/
def arrowCodRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels codRank problem
  | _, [] => .stuck
  | _, e :: rest =>
      match hd : readArrowCodEq e with
      | some _ => stepArrowCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening (viewOfArrowCodEq hd) rest
      | none => .stuck

/-- **The tree's driver on equations between arrow codes with codomains.** -/
def arrowCodSolver : ContextualDependentWorklist.Solver S.levels where
  rank := codRank
  round := arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
    strengthening

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
include total in
/-- **In the fragment, the conditions of narrowing and solving hold** once neither refutation applies. -/
theorem solvableCod_in_fragment {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices (e :: rest)) (v : FlexCod e)
    (none : (codHeads e.2.2.code).find? (misfitPred choices v.u) = none) :
    codSolvableB choices glb v = true := by
  simp only [codSolvableB, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, atUniversesB_of (inside.occurring e List.mem_cons_self).2⟩,
    sidesApartB_of (inside.apart e List.mem_cons_self)⟩
  · apply List.all_eq_true.mpr
    intro h member
    have typed := (inside.typedHeads e List.mem_cons_self).2 h member
    have notMisfit := List.find?_eq_none.mp none h member
    unfold fitPred
    unfold misfitPred at notMisfit
    cases hk : choices.typing h with
    | none => rw [hk] at typed; cases typed
    | some k =>
        rw [hk] at notMisfit
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at notMisfit
        exact decide_eq_true notMisfit
  · apply List.all_eq_true.mpr
    intro i _
    unfold codMeetsPred
    cases misfit : codMisfit (S := S) Θ.raw v.u e.2.2.code i with
    | false => rfl
    | true =>
        obtain ⟨w, hw, uw⟩ := (inside.occurring e List.mem_cons_self).2 i (codMisfit_mem misfit)
        obtain ⟨g, hg⟩ := total v.universe_u uw
        rw [codTarget_of_misfit glb misfit hw hg]
        rfl

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
include total in
theorem flexStepCod_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : FlexCod e) (ne : e.2.2.code ≠ .var v.X) (inside : InArrowsCod choices (e :: rest)) :
    flexStepCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared v ne rest ≠
      .stuck := by
  unfold flexStepCod
  by_cases hocc : v.X ∈ e.2.2.code.support
  · rw [dif_pos hocc]
    intro h; cases h
  · rw [dif_neg hocc]
    split
    · intro h; cases h
    · rename_i hmis
      have ok : codSolvableB choices glb v = true ∧ allArrowCodB rest = true :=
        ⟨solvableCod_in_fragment choices glb total inside v hmis, allArrowCodB_of (inArrowsCod_drop inside).codes⟩
      rw [dif_pos ok]
      intro h; cases h

omit [DecidableEq Head] [DecidableRel S.R.headEq] in
theorem flexStepCod_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : FlexCod e) (ne : e.2.2.code ≠ .var v.X) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (inside : InArrowsCod choices (e :: rest))
    (progressed : flexStepCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared v ne
      rest = .progress update smaller) : InArrowsCod choices update.remaining := by
  unfold flexStepCod at progressed
  by_cases hocc : v.X ∈ e.2.2.code.support
  · rw [dif_pos hocc] at progressed
    cases progressed
  · rw [dif_neg hocc] at progressed
    split at progressed
    · cases progressed
    · by_cases hok : codSolvableB choices glb v = true ∧ allArrowCodB rest = true
      · rw [dif_pos hok] at progressed
        cases progressed
        exact inArrowsCod_solved glb spec algebra inside v _
      · rw [dif_neg hok] at progressed
        cases progressed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem swapRoundCod_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {round : Round S.levels codRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest)} (moving : round ≠ .stuck) :
    swapRoundCod round ≠ .stuck := by
  cases round with
  | progress _ _ => intro h; cases h
  | refuted _ => intro h; cases h
  | stuck => exact absurd rfl moving

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq] in
theorem swapRoundCod_progress {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {round : Round S.levels codRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest)}
    {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (progressed : swapRoundCod round = .progress update smaller) :
    ∃ inner innerSmaller, round = .progress inner innerSmaller ∧
      update = inner.rephrase (swap_equivalent e rest) := by
  cases round with
  | progress inner innerSmaller =>
      cases progressed
      exact ⟨inner, innerSmaller, rfl, rfl⟩
  | refuted _ => cases progressed
  | stuck => cases progressed

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem rigidStepCod_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    (rest : EquationStore (TotalTerm Θ)) (notLeft : varOf e.1.2.code = none) (notRight : varOf e.2.2.code = none) :
    rigidStepCod facts roots heads algebra rigid complete headTypingUnique declared strengthening w rest ≠ .stuck := by
  have sl := rigidCodOf_code w.code_left notLeft
  have sr := rigidCodOf_code w.code_right notRight
  unfold rigidStepCod
  split
  · split_ifs <;> intro h <;> cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · exfalso
    simp_all
  · exfalso
    simp_all

omit [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem rigidStepCod_stable {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (w : ArrowCodEq e)
    {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (inside : InArrowsCod choices (e :: rest))
    (progressed : rigidStepCod facts roots heads algebra rigid complete headTypingUnique declared strengthening w
      rest = .progress update smaller) :
    InArrowsCod choices update.remaining := by
  unfold rigidStepCod at progressed
  split at progressed
  · split_ifs at progressed
    · cases progressed
      exact inArrowsCod_drop inside
    · cases progressed
      exact inArrowsCod_drop inside
  · cases progressed
  · cases progressed
  · cases progressed
    exact inArrowsCod_decompose algebra facts roots heads rigid complete headTypingUnique declared inside w _ _
  · cases progressed
  · cases progressed

include total in
theorem stepArrowCod_ne_stuck {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (w : ArrowCodEq e) (inside : InArrowsCod choices (e :: rest)) :
    stepArrowCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared strengthening w
      rest ≠ .stuck := by
  unfold stepArrowCod
  by_cases hsame : e.1.2.code = e.2.2.code
  · rw [dif_pos hsame]
    intro h; cases h
  · rw [dif_neg hsame]
    split
    · split
      · rename_i X hX u hu
        have memberX : X ∈ e.1.2.code.support := by
          rw [varOf_sound hX]
          exact Finset.mem_singleton_self _
        rw [dif_pos (universe_of_atUniverses (inside.occurring e List.mem_cons_self).1 memberX hu)]
        exact flexStepCod_ne_stuck choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          total _ _ inside
      · rename_i X hX hu
        exfalso
        have memberX : X ∈ e.1.2.code.support := by
          rw [varOf_sound hX]
          exact Finset.mem_singleton_self _
        obtain ⟨w', hw', _⟩ := (inside.occurring e List.mem_cons_self).1 X memberX
        unfold declaredUniverse at hu
        rw [hw'] at hu
        cases hu
    · split
      · split
        · rename_i Y hY u hu
          have memberY : Y ∈ e.2.2.code.support := by
            rw [varOf_sound hY]
            exact Finset.mem_singleton_self _
          rw [dif_pos (universe_of_atUniverses (inside.occurring e List.mem_cons_self).2 memberY hu)]
          exact swapRoundCod_ne_stuck (flexStepCod_ne_stuck choices glb spec facts roots heads algebra rigid complete
            headTypingUnique declared total _ _ (inArrowsCod_swap inside))
        · rename_i Y hY hu
          exfalso
          have memberY : Y ∈ e.2.2.code.support := by
            rw [varOf_sound hY]
            exact Finset.mem_singleton_self _
          obtain ⟨w', hw', _⟩ := (inside.occurring e List.mem_cons_self).2 Y memberY
          unfold declaredUniverse at hu
          rw [hw'] at hu
          cases hu
      · rename_i hX hY
        exact rigidStepCod_ne_stuck facts roots heads algebra rigid complete headTypingUnique declared strengthening w
          rest hX hY

theorem stepArrowCod_stable {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (w : ArrowCodEq e) {update : Update S.levels (e :: rest)}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank (e :: rest))}
    (inside : InArrowsCod choices (e :: rest))
    (progressed : stepArrowCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening w rest = .progress update smaller) : InArrowsCod choices update.remaining := by
  unfold stepArrowCod at progressed
  by_cases hsame : e.1.2.code = e.2.2.code
  · rw [dif_pos hsame] at progressed
    cases progressed
    exact inArrowsCod_drop inside
  · rw [dif_neg hsame] at progressed
    split at progressed
    · split at progressed
      · split_ifs at progressed
        exact flexStepCod_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared _ _
          inside progressed
      · cases progressed
    · split at progressed
      · split at progressed
        · split_ifs at progressed
          obtain ⟨inner, _, isInner, same⟩ := swapRoundCod_progress progressed
          subst same
          show InArrowsCod choices inner.remaining
          exact flexStepCod_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
            _ _ (inArrowsCod_swap inside) isInner
        · cases progressed
      · exact rigidStepCod_stable facts roots heads algebra rigid complete headTypingUnique declared strengthening w
          inside progressed

include total in
/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem arrowCodRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InArrowsCod choices problem) (nonempty : problem ≠ []) :
    arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared strengthening
      problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨w⟩ := inside.shapes e List.mem_cons_self
      have hd := readArrowCodEq_complete w
      simp only [arrowCodRound]
      split
      · exact stepArrowCod_ne_stuck choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening total _ inside
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem arrowCodRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (codRank update.remaining) (codRank problem)}
    (inside : InArrowsCod choices problem)
    (progressed : arrowCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening problem = .progress update smaller) :
    InArrowsCod choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [arrowCodRound] at progressed
      split at progressed
      · exact stepArrowCod_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening _ inside progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def arrowCodFragment :
    ContextualDependentWorklist.Fragment
      (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
        strengthening) where
  holds := InArrowsCod choices
  stable := fun inside progressed =>
    arrowCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening inside progressed
  decisive := fun inside nonempty =>
    arrowCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      strengthening total inside nonempty

include total in
/-- **Decided by shape, unknowns at domains and codomains**: on the fragment of equations between arrow codes with
codomains, the tree's driver with narrowing to greatest lower bounds, solving, decomposition and the refutations
reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem arrowsCod_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening) original larger =
        run (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          strengthening) original fuel ∧
        ((∃ state finished,
              run (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
                  strengthening) original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (arrowCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
              strengthening) original larger = .refuted absent)) :=
  (arrowCodFragment choices glb spec facts roots heads algebra rigid complete headTypingUnique declared strengthening
    total).decided inside

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- **Membership in the fragment of equations between arrow codes with codomains, decided.** -/
def inArrowsCodB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  problem.all (fun e => atUniversesB (S := S) Θ.raw e.1.2.code && atUniversesB (S := S) Θ.raw e.2.2.code &&
      sidesApartB Θ.raw e.1.2.code e.2.2.code) &&
    problem.all (fun e => (readArrowCodEq e).isSome) &&
    problem.all (fun e => (codHeads e.1.2.code).all (fun h => (choices.typing h).isSome) &&
      (codHeads e.2.2.code).all (fun h => (choices.typing h).isSome))

theorem inArrowsCod_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inArrowsCodB choices problem = true) : InArrowsCod choices problem := by
  simp only [inArrowsCodB, Bool.and_eq_true] at h
  obtain ⟨⟨hLocal, hShapes⟩, hHeads⟩ := h
  refine ⟨fun e member => ?_, fun e member => ?_, fun e member => ?_, fun e member => ?_⟩
  · have he := List.all_eq_true.mp hLocal e member
    simp only [Bool.and_eq_true] at he
    exact ⟨atUniverses_of_B he.1.1, atUniverses_of_B he.1.2⟩
  · have he := List.all_eq_true.mp hLocal e member
    simp only [Bool.and_eq_true] at he
    exact sidesApart_of_B he.2
  · have he := List.all_eq_true.mp hShapes e member
    cases hd : readArrowCodEq e with
    | none => rw [hd] at he; cases he
    | some v => exact ⟨viewOfArrowCodEq hd⟩
  · have he := List.all_eq_true.mp hHeads e member
    simp only [Bool.and_eq_true] at he
    exact ⟨fun h hh => List.all_eq_true.mp he.1 h hh, fun h hh => List.all_eq_true.mp he.2 h hh⟩

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
