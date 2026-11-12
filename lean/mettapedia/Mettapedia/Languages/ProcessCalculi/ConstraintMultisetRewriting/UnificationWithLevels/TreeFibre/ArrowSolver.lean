import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowRules

/-!
# The tree's driver on equations between arrow codes: first-order unification with universe levels, decided

A solver of the tree's driver (`arrowSolver`) on stores of equations between arrow codes at universes. On the first
equation it

* deletes it when its two sides have one code;
* when a side is an unknown `X`, refutes by the occurs check or a misfit head, or **narrows and solves** `X := t`
  (`narrowSolveUpdate`), in either orientation;
* when both sides are rigid, removes equal heads, **decomposes** two Π types with the same codomain head into their
  domains (`decomposeUpdate`), and refutes every clash.

Its rank is the number of unknowns occurring in the store, then the number of nodes of its sides: solving removes an
unknown from the store, every other step removes nodes.

**The fragment** (`InArrows`): every declaration is a universe and the declared universes are pairwise comparable;
every equation is between two arrow codes at a universe (`ArrowEq`); the heads of the sides have computed types.
Unlike `InFlexRigid`, no side has to be an unknown and an unknown may stand alone on several sides.

* Kept by every progress (`arrowRound_stable`); **progress by shape** (`arrowRound_ne_stuck`); **decided**
  (`arrows_decided`): at some budget and every larger one, a principal answer or a certified refutation.
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

/-! ## The rank -/

section Rank

theorem filter_length_le {α : Type} (l : List α) {p q : α → Bool} (sub : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ih' := ih (fun x m => sub x (List.mem_cons_of_mem _ m))
      cases hp : p a <;> cases hq : q a
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]
        exact ih'
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false, if_true, List.length_cons]
        omega
      · exact absurd (sub a List.mem_cons_self hp) (by rw [hq]; decide)
      · simp only [List.filter_cons, hp, hq, if_true, List.length_cons]
        omega

theorem filter_length_lt {α : Type} : ∀ (l : List α) {p q : α → Bool}, (∀ x ∈ l, p x = true → q x = true) →
    ∀ x ∈ l, q x = true → p x = false → (l.filter p).length < (l.filter q).length := by
  intro l
  induction l with
  | nil => intro p q _ x member; cases member
  | cons a l ih =>
      intro p q sub x member hq hp
      have sub' : ∀ y ∈ l, p y = true → q y = true := fun y m => sub y (List.mem_cons_of_mem _ m)
      rcases List.mem_cons.mp member with rfl | member
      · have le := filter_length_le l sub'
        simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false, if_true, List.length_cons]
        omega
      · have lt := ih sub' x member hq hp
        cases hpa : p a <;> cases hqa : q a
        · simp only [List.filter_cons, hpa, hqa, Bool.false_eq_true, if_false]
          exact lt
        · simp only [List.filter_cons, hpa, hqa, Bool.false_eq_true, if_false, if_true, List.length_cons]
          omega
        · exact absurd (sub a List.mem_cons_self hpa) (by rw [hqa]; decide)
        · simp only [List.filter_cons, hpa, hqa, if_true, List.length_cons]
          omega

theorem nodes_pos {n : Nat} (t : Tm Head n) : 1 ≤ nodes t := by
  cases t <;> simp [nodes]

/-- An unknown occurs in a side of a store, read along the domains. -/
def occursIn {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) (i : Fin Γ.arity) : Bool :=
  problem.any fun e => decide (i ∈ domainVars e.1.2.code) || decide (i ∈ domainVars e.2.2.code)

/-- The number of nodes of the sides of a store. -/
def storeSize {Γ : Context S.R} : EquationStore (TotalTerm Γ) → Nat
  | [] => 0
  | e :: rest => nodes e.1.2.code + nodes e.2.2.code + storeSize rest

/-- **The rank**: the number of unknowns occurring in the store, then its size. -/
def arrowRank {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Nat × Nat :=
  (((List.finRange Γ.arity).filter (occursIn problem)).length, storeSize problem)

theorem below_of_le_lt {a b c d : Nat} (first : a ≤ c) (second : b < d) :
    ContextualDependentWorklist.Below (a, b) (c, d) := by
  rcases Nat.lt_or_eq_of_le first with lt | rfl
  · exact Prod.Lex.left _ _ lt
  · exact Prod.Lex.right _ second

theorem occursIn_cons {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ))
    (i : Fin Γ.arity) :
    occursIn (e :: rest) i = true ↔
      (i ∈ domainVars e.1.2.code ∨ i ∈ domainVars e.2.2.code) ∨ occursIn rest i = true := by
  simp [occursIn, List.any_cons]

/-- **Removing the first equation lowers the rank.** -/
theorem rank_drop {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ)) :
    ContextualDependentWorklist.Below (arrowRank rest) (arrowRank (e :: rest)) := by
  refine below_of_le_lt (filter_length_le _ fun i _ h => (occursIn_cons e rest i).mpr (.inr h)) ?_
  have := nodes_pos e.1.2.code
  simp only [storeSize]
  omega

/-- **Swapping the sides of the first equation keeps the rank.** -/
theorem arrowRank_swap {Γ : Context S.R} (e : Equation (TotalTerm Γ)) (rest : EquationStore (TotalTerm Γ)) :
    arrowRank (((e.2, e.1) : Equation (TotalTerm Γ)) :: rest) = arrowRank (e :: rest) := by
  have occ : occursIn (((e.2, e.1) : Equation (TotalTerm Γ)) :: rest) = occursIn (e :: rest) := by
    funext i
    simp only [occursIn, List.any_cons, Bool.or_comm]
  unfold arrowRank
  rw [occ]
  simp only [storeSize]
  congr 1
  omega

end Rank

/-! ## Solving lowers the rank -/

section SolveRank

variable [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- Every side of the store is an arrow code. -/
def AllArrows {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Prop :=
  ∀ e ∈ problem, Arrow e.1.2.code ∧ Arrow e.2.2.code

/-- Whether every side of the store is an arrow code, decided. -/
def allArrowsB {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Bool :=
  problem.all fun e => isArrow e.1.2.code && isArrow e.2.2.code

omit [DecidableRel S.R.cumulative] in
theorem allArrows_of_B {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (h : allArrowsB problem = true) :
    AllArrows problem := by
  intro e member
  have he := List.all_eq_true.mp h e member
  simp only [Bool.and_eq_true] at he
  exact ⟨arrow_of_isArrow he.1, arrow_of_isArrow he.2⟩

omit [DecidableRel S.R.cumulative] in
theorem allArrowsB_of {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} (h : AllArrows problem) :
    allArrowsB problem = true := by
  apply List.all_eq_true.mpr
  intro e member
  simp only [Bool.and_eq_true]
  exact ⟨isArrow_of_arrow (h e member).1, isArrow_of_arrow (h e member).2⟩

/-- **After narrowing and solving, the unknowns occurring are among those before, without the solved one.** -/
theorem occursIn_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    {rest : EquationStore (TotalTerm Θ)} (arrows : AllArrows rest) (i : Fin Θ.arity)
    (after : occursIn ((frames S.levels).applyStore (narrowSolve algebra v ok) rest) i = true) :
    occursIn (e :: rest) i = true ∧ i ≠ v.X := by
  simp only [occursIn, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq] at after
  obtain ⟨e'', member, hit⟩ := after
  obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
  obtain ⟨arrowL, arrowR⟩ := arrows e' inRest
  have sides : ∀ (c : Tm Head Θ.arity), Arrow c → i ∈ domainVars (Presentation.subst (solveSub v.X e.2.2.code) c) →
      (i ∈ domainVars c ∧ i ≠ v.X) ∨ i ∈ domainVars e.2.2.code := fun c arrow inside =>
    domainVars_subst_solve arrow i inside
  have inside : (i ∈ domainVars e'.1.2.code ∧ i ≠ v.X) ∨ (i ∈ domainVars e'.2.2.code ∧ i ≠ v.X) ∨
      i ∈ domainVars e.2.2.code := by
    rcases hit with hitL | hitR
    · rcases sides _ arrowL hitL with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · rcases sides _ arrowR hitR with h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
  rcases inside with ⟨h, ne⟩ | ⟨h, ne⟩ | h
  · refine ⟨(occursIn_cons e rest i).mpr (.inr ?_), ne⟩
    simp only [occursIn, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨e', inRest, .inl h⟩
  · refine ⟨(occursIn_cons e rest i).mpr (.inr ?_), ne⟩
    simp only [occursIn, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨e', inRest, .inr h⟩
  · exact ⟨(occursIn_cons e rest i).mpr (.inl (.inr h)), fun same => ok.absent (same ▸ h)⟩

/-- **Narrowing and solving lowers the rank.** -/
theorem rank_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    {rest : EquationStore (TotalTerm Θ)} (arrows : AllArrows rest) :
    ContextualDependentWorklist.Below (arrowRank ((frames S.levels).applyStore (narrowSolve algebra v ok) rest))
      (arrowRank (e :: rest)) := by
  apply Prod.Lex.left
  apply filter_length_lt (List.finRange Θ.arity) (fun i _ h => (occursIn_solved algebra v ok arrows i h).1) v.X
    (List.mem_finRange v.X)
  · apply (occursIn_cons e rest v.X).mpr
    left
    left
    rw [v.side_left]
    exact List.mem_singleton_self _
  · cases h : occursIn ((frames S.levels).applyStore (narrowSolve algebra v ok) rest) v.X with
    | false => rfl
    | true => exact absurd rfl (occursIn_solved algebra v ok arrows v.X h).2

end SolveRank

/-! ## The fragment -/

section Fragment

/-- **The fragment of equations between arrow codes.** -/
structure InArrows (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  universes : AllUniverseDecls Θ
  chain : Chain Θ
  shapes : ∀ e ∈ problem, Nonempty (ArrowEq e)
  typedHeads : ∀ e ∈ problem, (∀ h ∈ arrowHeads e.1.2.code, (choices.typing h).isSome = true) ∧
    (∀ h ∈ arrowHeads e.2.2.code, (choices.typing h).isSome = true)

theorem InArrows.arrows {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InArrows choices problem) : AllArrows problem := by
  intro e member
  obtain ⟨w⟩ := inside.shapes e member
  exact ⟨w.arrow_left, w.arrow_right⟩

theorem inArrows_drop {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrows choices (e :: rest)) :
    InArrows choices rest :=
  ⟨inside.universes, inside.chain, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.typedHeads e' (List.mem_cons_of_mem _ member)⟩

theorem inArrows_swap {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrows choices (e :: rest)) :
    InArrows choices (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) := by
  refine ⟨inside.universes, inside.chain, fun e' member => ?_, fun e' member => ?_⟩
  · rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨w⟩ := inside.shapes e List.mem_cons_self
      exact ⟨w.swap⟩
    · exact inside.shapes e' (List.mem_cons_of_mem _ member)
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨(inside.typedHeads e List.mem_cons_self).2, (inside.typedHeads e List.mem_cons_self).1⟩
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ member)

variable [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- **Narrowing and solving keeps the fragment.** -/
theorem inArrows_solved {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InArrows choices (e :: rest))
    (v : FlexArrow e) (ok : Solvable' v) :
    InArrows choices ((frames S.levels).applyStore (narrowSolve algebra v ok) rest) := by
  refine ⟨?_, narrowed_chain v ok inside.chain, ?_, ?_⟩
  · intro i
    rcases narrowed_lookup v ok i with ⟨_, low⟩ | ⟨_, same⟩
    · exact ⟨v.u, low, v.universe_u⟩
    · obtain ⟨w, hw, uw⟩ := inside.universes i
      exact ⟨w, same.trans hw, uw⟩
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
      arrow_left := arrow_subst_solve v.arrow w.arrow_left
      arrow_right := arrow_subst_solve v.arrow w.arrow_right }⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    have heads' := inside.typedHeads e' (List.mem_cons_of_mem _ inRest)
    have headsE := (inside.typedHeads e List.mem_cons_self).2
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · rcases arrowHeads_subst_solve w.arrow_left h hh with inner | fromT
      · exact heads'.1 h inner
      · exact headsE h fromT
    · rcases arrowHeads_subst_solve w.arrow_right h hh with inner | fromT
      · exact heads'.2 h inner
      · exact headsE h fromT

end Fragment

/-! ## Rigid arrow codes -/

section RigidCodes

/-- The two rigid shapes of an arrow code. -/
inductive Rigid (Head : Type) (n : Nat) where
  | head (h : Head)
  | pi (A : Tm Head n) (h : Head)

/-- Read the rigid shape of a code. -/
def rigidOf {n : Nat} : Tm Head n → Option (Rigid Head n)
  | .head h => some (.head h)
  | .pi A (.head h) => some (.pi A h)
  | _ => none

theorem rigidOf_head {n : Nat} {t : Tm Head n} {h : Head} (found : rigidOf t = some (.head h)) : t = .head h := by
  unfold rigidOf at found
  split at found
  · cases found; rfl
  · cases found
  · cases found

theorem rigidOf_pi {n : Nat} {t : Tm Head n} {A : Tm Head n} {h : Head} (found : rigidOf t = some (.pi A h)) :
    t = .pi A (.head h) := by
  unfold rigidOf at found
  split at found
  · cases found
  · cases found; rfl
  · cases found

/-- **An arrow code that is not an unknown has a rigid shape.** -/
theorem rigidOf_arrow {n : Nat} {t : Tm Head n} (arrow : Arrow t) (notVar : varOf t = none) :
    (rigidOf t).isSome = true := by
  cases arrow with
  | var Y => cases notVar
  | head h => rfl
  | pi h _ => rfl

/-- The domain of an arrow code of a Π type is an arrow code. -/
theorem arrow_domain {n : Nat} {A : Tm Head n} {h : Head} (arrow : Arrow (.pi A (.head h))) : Arrow A := by
  cases arrow with
  | pi _ inner => exact inner

end RigidCodes

/-! ## The solver -/

section Solver

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
  [DecidableRel S.R.headEq]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The view of an equation whose left side is an unknown declared at a universe. -/
def flexLeft {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {X : Fin Θ.arity} {u : Head}
    (hX : varOf e.1.2.code = some X) (hu : declaredUniverse Θ.raw X = some u) (huu : S.R.isUniverse u) :
    FlexArrow e :=
  ⟨w.v, X, u, w.annotation_left, w.annotation_right, varOf_sound hX, headOf_sound hu, huu, w.universe_v,
    w.arrow_right⟩

/-- **The step on an equation with an unknown on the left**: occurs or misfit refutation, or narrow and solve. -/
def flexStep {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ne : e.2.2.code ≠ .var v.X)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels arrowRank (e :: rest) :=
  if hocc : v.X ∈ domainVars e.2.2.code then
    .refuted (occurs_refutes facts roots heads algebra rigid complete v hocc ne rest)
  else match hmis : (arrowHeads e.2.2.code).find? (misfitPred choices v.u) with
    | some _ =>
        .refuted (misfit_refutes facts roots heads algebra rigid complete v (List.mem_of_find?_eq_some hmis)
          (misfit_apart choices headTypingUnique (List.find?_some hmis)) rest)
    | none =>
        if hok : solvableB choices v = true ∧ allArrowsB rest = true then
          .progress (narrowSolveUpdate facts roots heads algebra rigid complete v
              (solvable_of_B choices v hok.1 hocc) rest)
            (rank_solved algebra v (solvable_of_B choices v hok.1 hocc) (allArrows_of_B hok.2))
        else .stuck

/-- A round on the swapped equation, read on the equation. -/
def swapRound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} :
    Round S.levels arrowRank (((e.2, e.1) : Equation (TotalTerm Θ)) :: rest) → Round S.levels arrowRank (e :: rest)
  | .progress update smaller =>
      .progress (update.rephrase (swap_equivalent e rest)) (by
        have same := arrowRank_swap e rest
        change ContextualDependentWorklist.Below (arrowRank update.remaining) (arrowRank (e :: rest))
        rw [← same]
        exact smaller)
  | .refuted absent =>
      .refuted (fun ⟨Δ, σ, models⟩ => absent ⟨Δ, σ, (swap_equivalent e rest Δ σ).mp models⟩)
  | .stuck => .stuck

/-- **The step on two rigid sides**: equal heads, decomposition, or a clash. -/
def rigidStep {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) (rest : EquationStore (TotalTerm Θ)) :
    Round S.levels arrowRank (e :: rest) :=
  match hl : rigidOf e.1.2.code, hr : rigidOf e.2.2.code with
  | some (.head h), some (.head h') =>
      if same : h = h' then
        .progress (deleteCodes e (w.annotation_left.trans w.annotation_right.symm)
            (by rw [rigidOf_head hl, rigidOf_head hr, same]) rest)
          (rank_drop e rest)
      else if equal : S.R.headEq h h' then
        .progress (headEqUpdate facts algebra w (rigidOf_head hl) (rigidOf_head hr) equal rest) (rank_drop e rest)
      else .refuted (headClash_refutes facts w (rigidOf_head hl) (rigidOf_head hr)
        (fun hs => by rcases hs with h₁ | h₂ <;> contradiction) rest)
  | some (.head _), some (.pi _ _) => .refuted (headPi_refutes facts w (rigidOf_head hl) (rigidOf_pi hr) rest)
  | some (.pi _ _), some (.head _) => .refuted (piHead_refutes facts w (rigidOf_pi hl) (rigidOf_head hr) rest)
  | some (.pi A h), some (.pi A' h') =>
      if same : h = h' ∨ S.R.headEq h h' then
        .progress (decomposeUpdate facts roots heads algebra rigid complete w (rigidOf_pi hl) (rigidOf_pi hr) same
            rest) (by
          refine below_of_le_lt (filter_length_le _ fun i _ inside => ?_) ?_
          · rcases (occursIn_cons _ rest i).mp inside with hit | hit
            · apply (occursIn_cons e rest i).mpr
              left
              rw [rigidOf_pi hl, rigidOf_pi hr]
              exact hit
            · exact (occursIn_cons e rest i).mpr (.inr hit)
          · show nodes A + nodes A' + storeSize rest < nodes e.1.2.code + nodes e.2.2.code + storeSize rest
            rw [rigidOf_pi hl, rigidOf_pi hr]
            simp only [nodes]
            omega)
      else .refuted (codomainClash_refutes facts w (rigidOf_pi hl) (rigidOf_pi hr) same rest)
  | none, _ => .stuck
  | some _, none => .stuck

/-- **One step on a read equation.** -/
def stepArrow {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) (rest : EquationStore (TotalTerm Θ)) :
    Round S.levels arrowRank (e :: rest) :=
  if hsame : e.1.2.code = e.2.2.code then
    .progress (deleteCodes e (w.annotation_left.trans w.annotation_right.symm) hsame rest) (rank_drop e rest)
  else match hX : varOf e.1.2.code with
    | some X =>
        match hu : declaredUniverse Θ.raw X with
        | some u =>
            if huu : S.R.isUniverse u then
              flexStep choices facts roots heads algebra rigid complete headTypingUnique (flexLeft w hX hu huu)
                (fun same => hsame ((varOf_sound hX).trans same.symm)) rest
            else .stuck
        | none => .stuck
    | none =>
        match hY : varOf e.2.2.code with
        | some Y =>
            match hu : declaredUniverse Θ.raw Y with
            | some u =>
                if huu : S.R.isUniverse u then
                  swapRound (flexStep choices facts roots heads algebra rigid complete headTypingUnique
                    (flexLeft w.swap hY hu huu) (fun same => hsame ((varOf_sound hY).trans same.symm).symm) rest)
                else .stuck
            | none => .stuck
        | none => rigidStep facts roots heads algebra rigid complete w rest

end Solver

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
