import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigid

/-!
# The tree's driver on flex-rigid stores: progress by shape, with meet narrowing and two refutations

A solver of the tree's driver (`flexRigidSolver`) reads the first equation `X ≐ t` (`readFlexArrow`) and

* deletes it when `t` is `X`;
* **refutes** the store when `X` occurs along the domains of `t` (the occurs check), or when a head of `t` is typed by
  no universe below `X`'s (a misfit), each with a certificate;
* otherwise **narrows and solves**: every unknown of `t` declared above `X`'s universe is declared again at it, and
  `X := t` (`narrowSolveUpdate`);
* is stuck only when a declared universe is incomparable with `X`'s, or a head's type is not computed.

**The fragment** (`InFlexRigid`): every declaration is a universe, and the declared universes are pairwise comparable;
every equation is a flex-rigid equation of a universe unknown and an arrow code (`FlexArrow`); the heads of the right
sides have computed types; and the left unknowns of the equations are pairwise distinct.

* Kept by every progress (`flexRigidRound_stable`): narrowing lowers unknowns to a declared universe, so the chain
  stays a chain; solving `X := t` keeps arrow codes, and the left unknowns are untouched.
* **Progress by shape** (`flexRigidRound_ne_stuck`), and **decided** (`flexRigid_decided`): on the fragment the driver
  reaches, at some budget and every larger one, a principal answer or a certified refutation; both occur.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Reading -/

section Reading

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- The data of a flex-rigid reading. -/
structure FlexArrowData (Head : Type) (n : Nat) where
  v : Head
  X : Fin n
  u : Head

/-- **Read a flex-rigid equation of a universe unknown and an arrow code** off its codes. -/
def readFlexArrow {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (FlexArrowData Head Θ.arity) :=
  (headOf e.1.1.code).bind fun v =>
  (varOf e.1.2.code).bind fun X =>
  (declaredUniverse Θ.raw X).bind fun u =>
  if e.2.1.code = .head v ∧ S.R.isUniverse u ∧ S.R.isUniverse v ∧ isArrow e.2.2.code = true then some ⟨v, X, u⟩
  else none

theorem readFlexArrow_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexArrowData Head Θ.arity}
    (h : readFlexArrow e = some d) :
    e.1.1.code = .head d.v ∧ e.1.2.code = .var d.X ∧ Ctx.lookup Θ.raw d.X = .head d.u ∧ e.2.1.code = .head d.v ∧
      S.R.isUniverse d.u ∧ S.R.isUniverse d.v ∧ Arrow e.2.2.code := by
  unfold readFlexArrow at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, X, hX, u, hu, h⟩ := h
  split_ifs at h with hc
  cases h
  exact ⟨headOf_sound hv, varOf_sound hX, headOf_sound hu, hc.1, hc.2.1, hc.2.2.1, arrow_of_isArrow hc.2.2.2⟩

/-- The view of a successful reading. -/
def viewOfArrow {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : FlexArrowData Head Θ.arity}
    (h : readFlexArrow e = some d) : FlexArrow e where
  v := d.v
  X := d.X
  u := d.u
  annotation_left := (readFlexArrow_sound h).1
  annotation_right := (readFlexArrow_sound h).2.2.2.1
  side_left := (readFlexArrow_sound h).2.1
  declared := (readFlexArrow_sound h).2.2.1
  universe_u := (readFlexArrow_sound h).2.2.2.2.1
  universe_v := (readFlexArrow_sound h).2.2.2.2.2.1
  arrow := (readFlexArrow_sound h).2.2.2.2.2.2

/-- **The reader reads every flex-rigid equation.** -/
theorem readFlexArrow_complete {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) :
    readFlexArrow e = some ⟨v.v, v.X, v.u⟩ := by
  unfold readFlexArrow
  rw [v.annotation_left, v.side_left]
  simp [headOf, varOf, declaredUniverse, v.declared, v.annotation_right, v.universe_u, v.universe_v,
    isArrow_of_arrow v.arrow]

end Reading

/-- **The reading of an equation is unique.** -/
theorem FlexArrow.unique {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v w : FlexArrow e) : v.X = w.X :=
  Tm.var.inj (v.side_left.symm.trans w.side_left)

/-! ## The fragment -/

section Fragment

/-- The declared universes are pairwise comparable. -/
def Chain (Θ : Context S.R) : Prop :=
  ∀ (i j : Fin Θ.arity) (w w' : Head), Ctx.lookup Θ.raw i = .head w → Ctx.lookup Θ.raw j = .head w' →
    S.R.cumulative w w' ∨ S.R.cumulative w' w

/-- **The fragment of flex-rigid stores.** -/
structure InFlexRigid (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  universes : AllUniverseDecls Θ
  chain : Chain Θ
  shapes : ∀ e ∈ problem, Nonempty (FlexArrow e)
  typedHeads : ∀ e ∈ problem, ∀ h ∈ arrowHeads e.2.2.code, (choices.typing h).isSome = true
  distinct : problem.Pairwise (fun e₁ e₂ => ∀ (v₁ : FlexArrow e₁) (v₂ : FlexArrow e₂), v₁.X ≠ v₂.X)

theorem inFlexRigid_delete {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexRigid choices (e :: rest)) :
    InFlexRigid choices rest :=
  ⟨inside.universes, inside.chain, fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.typedHeads e' (List.mem_cons_of_mem _ member), (List.pairwise_cons.mp inside.distinct).2⟩

variable [DecidableRel S.R.cumulative] (algebra : CumulativeAlgebra S.R)

/-- The declaration of an unknown after narrowing: the universe of `X` where it was a misfit, unchanged otherwise. -/
theorem narrowed_lookup {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    (i : Fin Θ.arity) :
    (misfitSet (S := S) Θ.raw v.u e.2.2.code i = true ∧ Ctx.lookup (narrowed v ok).raw i = .head v.u) ∨
      (misfitSet (S := S) Θ.raw v.u e.2.2.code i = false ∧ Ctx.lookup (narrowed v ok).raw i = Ctx.lookup Θ.raw i) := by
  cases inside : misfitSet (S := S) Θ.raw v.u e.2.2.code i with
  | true => exact .inl ⟨rfl, lookup_lowerSet_in Θ.raw _ v.u i inside⟩
  | false => exact .inr ⟨rfl, lookup_lowerSet_out Θ.raw _ v.u i inside⟩

/-- **The view of an equation after narrowing and solving.** -/
theorem narrowSolve_view {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    (w : FlexArrow e') (ne : w.X ≠ v.X) :
    ∃ t : FlexArrow (((frames S.levels).act (narrowSolve algebra v ok) e'.1,
        (frames S.levels).act (narrowSolve algebra v ok) e'.2) : Equation (TotalTerm (narrowed v ok))), t.X = w.X := by
  have declared : ∃ u', Ctx.lookup (narrowed v ok).raw w.X = .head u' ∧ S.R.isUniverse u' := by
    rcases narrowed_lookup v ok w.X with ⟨_, low⟩ | ⟨_, same⟩
    · exact ⟨v.u, low, v.universe_u⟩
    · exact ⟨w.u, same.trans w.declared, w.universe_u⟩
  obtain ⟨u', hu', uu'⟩ := declared
  exact ⟨{
    v := w.v
    X := w.X
    u := u'
    annotation_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.1.code = .head w.v
      rw [w.annotation_left]
      rfl
    annotation_right := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.2.1.code = .head w.v
      rw [w.annotation_right]
      rfl
    side_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.2.code = .var w.X
      rw [w.side_left]
      exact solveSub_ne _ ne
    declared := hu'
    universe_u := uu'
    universe_v := w.universe_v
    arrow := arrow_subst_solve v.arrow w.arrow }, rfl⟩

/-- **Narrowing keeps the chain**: a lowered unknown takes the universe of a declared unknown. -/
theorem narrowed_chain {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) (ok : Solvable' v)
    (chain : Chain Θ) : Chain (narrowed v ok) := by
  have below : ∀ (i : Fin Θ.arity) (a : Head), Ctx.lookup (narrowed v ok).raw i = .head a →
      Ctx.lookup Θ.raw i = .head a ∨ a = v.u := by
    intro i a ha
    rcases narrowed_lookup v ok i with ⟨_, low⟩ | ⟨_, same⟩
    · exact .inr (Tm.head.inj (ha.symm.trans low))
    · exact .inl (same.symm.trans ha)
  intro i j a b ha hb
  rcases below i a ha with ha' | rfl
  · rcases below j b hb with hb' | rfl
    · exact chain i j a b ha' hb'
    · exact chain i v.X a v.u ha' v.declared
  · rcases below j b hb with hb' | rfl
    · exact chain v.X j v.u b v.declared hb'
    · exact .inl (S.levels.cumulative_refl v.universe_u)

/-- **Narrowing and solving keeps the fragment.** -/
theorem inFlexRigid_narrowSolve {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexRigid choices (e :: rest))
    (v : FlexArrow e) (ok : Solvable' v) :
    InFlexRigid choices ((frames S.levels).applyStore (narrowSolve algebra v ok) rest) := by
  have tail := List.pairwise_cons.mp inside.distinct
  refine ⟨?_, narrowed_chain v ok inside.chain, ?_, ?_, ?_⟩
  · intro i
    rcases narrowed_lookup v ok i with ⟨_, low⟩ | ⟨_, same⟩
    · exact ⟨v.u, low, v.universe_u⟩
    · obtain ⟨w, hw, uw⟩ := inside.universes i
      exact ⟨w, same.trans hw, uw⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _⟩ := narrowSolve_view algebra v ok w (fun same => tail.1 e' inRest v w same.symm)
    exact ⟨t⟩
  · intro e'' member h hh
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    rcases arrowHeads_subst_solve w.arrow h hh with fromE' | fromE
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ inRest) h fromE'
    · exact inside.typedHeads e List.mem_cons_self h fromE
  · refine List.pairwise_map.mpr (tail.2.imp_of_mem ?_)
    intro e₁ e₂ m₁ m₂ apart t₁ t₂
    obtain ⟨w₁⟩ := inside.shapes e₁ (List.mem_cons_of_mem _ m₁)
    obtain ⟨w₂⟩ := inside.shapes e₂ (List.mem_cons_of_mem _ m₂)
    obtain ⟨s₁, h₁⟩ := narrowSolve_view algebra v ok w₁ (fun same => tail.1 e₁ m₁ v w₁ same.symm)
    obtain ⟨s₂, h₂⟩ := narrowSolve_view algebra v ok w₂ (fun same => tail.1 e₂ m₂ v w₂ same.symm)
    rw [FlexArrow.unique t₁ s₁, FlexArrow.unique t₂ s₂, h₁, h₂]
    exact apart w₁ w₂

end Fragment

/-! ## The solver -/

section Solver

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- A head whose computed type does not lie below `u`. -/
def misfitPred (u : Head) (h : Head) : Bool :=
  match choices.typing h with
  | some k => !decide (S.R.cumulative k.1 u)
  | none => false

/-- A head whose computed type lies below `u`. -/
def fitPred (u : Head) (h : Head) : Bool :=
  match choices.typing h with
  | some k => decide (S.R.cumulative k.1 u)
  | none => false

/-- An unknown declared at a universe comparable with `u`. -/
def comparablePred {n : Nat} (Γ : Ctx Head n) (u : Head) (Y : Fin n) : Bool :=
  match declaredUniverse Γ Y with
  | some w => decide (S.R.cumulative w u) || decide (S.R.cumulative u w)
  | none => false

/-- Whether every declaration is a universe, decided. -/
def allUniverseDeclsB (Θ : Context S.R) : Bool :=
  (List.finRange Θ.arity).all fun i => match declaredUniverse Θ.raw i with
    | some w => decide (S.R.isUniverse w)
    | none => false

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
theorem allUniverseDecls_of_B {Θ : Context S.R} (h : allUniverseDeclsB Θ = true) : AllUniverseDecls Θ := by
  intro i
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  cases hd : declaredUniverse Θ.raw i with
  | none => rw [hd] at hi; cases hi
  | some w =>
      rw [hd] at hi
      exact ⟨w, headOf_sound hd, of_decide_eq_true hi⟩

omit [DecidableEq Head] [DecidableRel S.R.cumulative] in
theorem allUniverseDeclsB_of {Θ : Context S.R} (all : AllUniverseDecls Θ) : allUniverseDeclsB Θ = true := by
  apply List.all_eq_true.mpr
  intro i _
  obtain ⟨w, hw, uw⟩ := all i
  have hd : declaredUniverse Θ.raw i = some w := by unfold declaredUniverse; rw [hw]; rfl
  rw [hd]
  exact decide_eq_true uw

/-- **The conditions of narrow-and-solve, decided.** -/
def solvableB {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : Bool :=
  (arrowHeads e.2.2.code).all (fitPred choices v.u) &&
    (domainVars e.2.2.code).all (comparablePred (S := S) Θ.raw v.u) && allUniverseDeclsB Θ

omit [DecidableEq Head] in
theorem solvable_of_B {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (h : solvableB choices v = true) (absent : v.X ∉ domainVars e.2.2.code) : Solvable' v := by
  simp only [solvableB, Bool.and_eq_true] at h
  obtain ⟨⟨hHeads, hComparable⟩, hAll⟩ := h
  refine ⟨absent, ?_, allUniverseDecls_of_B hAll, ?_⟩
  · intro h member
    have fit := List.all_eq_true.mp hHeads h member
    unfold fitPred at fit
    cases hk : choices.typing h with
    | none => rw [hk] at fit; cases fit
    | some k =>
        rw [hk] at fit
        exact ⟨k.1, k.2, of_decide_eq_true fit⟩
  · intro Y member w hw
    have comparable := List.all_eq_true.mp hComparable Y member
    unfold comparablePred declaredUniverse at comparable
    rw [hw] at comparable
    simp only [headOf, Bool.or_eq_true, decide_eq_true_eq] at comparable
    exact comparable

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include headTypingUnique in
/-- A head found by the misfit test is typed by no universe below `u`. -/
theorem misfit_apart {u h₀ : Head} (found : misfitPred choices u h₀ = true) :
    ∀ k, S.R.headTyping h₀ k → ¬ S.R.cumulative k u := by
  intro k typing below
  unfold misfitPred at found
  cases hk : choices.typing h₀ with
  | none => rw [hk] at found; cases found
  | some k' =>
      rw [hk] at found
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at found
      exact found (headTypingUnique k'.2 typing ▸ below)

/-- **One step on a read equation**: delete, refute by occurs or misfit, narrow and solve, or stuck. -/
def stepFlexRigid {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hdel : e.2.2.code = .var v.X then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm) (v.side_left.trans hdel.symm) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hocc : v.X ∈ domainVars e.2.2.code then
    .refuted (occurs_refutes facts roots heads algebra rigid complete v hocc hdel rest)
  else match hmis : (arrowHeads e.2.2.code).find? (misfitPred choices v.u) with
    | some h₀ =>
        .refuted (misfit_refutes facts roots heads algebra rigid complete v (List.mem_of_find?_eq_some hmis)
          (misfit_apart choices headTypingUnique (List.find?_some hmis)) rest)
    | none =>
        if hok : solvableB choices v = true then
          .progress (narrowSolveUpdate facts roots heads algebra rigid complete v (solvable_of_B choices v hok hocc)
              rest)
            (below_of_length (by
              show ((frames S.levels).applyStore _ rest).length < (e :: rest).length
              simp [Frames.applyStore]))
        else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def flexRigidRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | _, e :: rest =>
      match hd : readFlexArrow e with
      | some _ => stepFlexRigid choices facts roots heads algebra rigid complete headTypingUnique (viewOfArrow hd) rest
      | none => .stuck

/-- **The tree's driver on flex-rigid stores.** -/
def flexRigidSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := flexRigidRound choices facts roots heads algebra rigid complete headTypingUnique

/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem flexRigidRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InFlexRigid choices problem) (nonempty : problem ≠ []) :
    flexRigidRound choices facts roots heads algebra rigid complete headTypingUnique problem ≠ .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      have hd := readFlexArrow_complete v
      simp only [flexRigidRound]
      split
      · rename_i d hd'
        unfold stepFlexRigid
        by_cases hdel : e.2.2.code = .var (viewOfArrow hd').X
        · rw [dif_pos hdel]
          intro h; cases h
        · rw [dif_neg hdel]
          by_cases hocc : (viewOfArrow hd').X ∈ domainVars e.2.2.code
          · rw [dif_pos hocc]
            intro h; cases h
          · rw [dif_neg hocc]
            split
            · intro h; cases h
            · rename_i hmis
              -- the conditions of narrow-and-solve hold in the fragment
              have ok : solvableB choices (viewOfArrow hd') = true := by
                simp only [solvableB, Bool.and_eq_true]
                refine ⟨⟨?_, ?_⟩, allUniverseDeclsB_of inside.universes⟩
                · apply List.all_eq_true.mpr
                  intro h member
                  have typed := inside.typedHeads e List.mem_cons_self h member
                  have notMisfit := List.find?_eq_none.mp hmis h member
                  unfold fitPred
                  unfold misfitPred at notMisfit
                  cases hk : choices.typing h with
                  | none => rw [hk] at typed; cases typed
                  | some k =>
                      rw [hk] at notMisfit
                      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at notMisfit
                      exact decide_eq_true notMisfit
                · apply List.all_eq_true.mpr
                  intro Y _
                  obtain ⟨w, hw, _⟩ := inside.universes Y
                  unfold comparablePred declaredUniverse
                  rw [hw]
                  simp only [headOf, Bool.or_eq_true, decide_eq_true_eq]
                  exact inside.chain Y (viewOfArrow hd').X w (viewOfArrow hd').u hw (viewOfArrow hd').declared
              rw [dif_pos ok]
              intro h; cases h
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem flexRigidRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFlexRigid choices problem)
    (progressed : flexRigidRound choices facts roots heads algebra rigid complete headTypingUnique problem =
      .progress update smaller) :
    InFlexRigid choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [flexRigidRound] at progressed
      split at progressed
      · rename_i d hd
        unfold stepFlexRigid at progressed
        by_cases hdel : e.2.2.code = .var (viewOfArrow hd).X
        · rw [dif_pos hdel] at progressed
          cases progressed
          exact inFlexRigid_delete inside
        · rw [dif_neg hdel] at progressed
          by_cases hocc : (viewOfArrow hd).X ∈ domainVars e.2.2.code
          · rw [dif_pos hocc] at progressed
            cases progressed
          · rw [dif_neg hocc] at progressed
            split at progressed
            · cases progressed
            · by_cases hok : solvableB choices (viewOfArrow hd) = true
              · rw [dif_pos hok] at progressed
                cases progressed
                exact inFlexRigid_narrowSolve algebra inside (viewOfArrow hd) _
              · rw [dif_neg hok] at progressed
                cases progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def flexRigidFragment :
    ContextualDependentWorklist.Fragment
      (flexRigidSolver choices facts roots heads algebra rigid complete headTypingUnique) where
  holds := InFlexRigid choices
  stable := fun inside progressed =>
    flexRigidRound_stable choices facts roots heads algebra rigid complete headTypingUnique inside progressed
  decisive := fun inside nonempty =>
    flexRigidRound_ne_stuck choices facts roots heads algebra rigid complete headTypingUnique inside nonempty

include facts roots heads algebra rigid complete headTypingUnique in
/-- **Decided by shape**: on the fragment of flex-rigid stores, the tree's driver with meet narrowing, solving and the
two refutations reaches, at some budget and at every larger one, a principal answer or a certified refutation. -/
theorem flexRigid_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexRigid choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (flexRigidSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
          run (flexRigidSolver choices facts roots heads algebra rigid complete headTypingUnique) original fuel ∧
        ((∃ state finished,
              run (flexRigidSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
                .solved state finished ∧ (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (flexRigidSolver choices facts roots heads algebra rigid complete headTypingUnique) original larger =
              .refuted absent)) :=
  (flexRigidFragment choices facts roots heads algebra rigid complete headTypingUnique).decided inside

end Solver

/-! ## Membership, decided -/

section Membership

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- The declared universes are pairwise comparable, decided. -/
def chainB (Θ : Context S.R) : Bool :=
  (List.finRange Θ.arity).all fun i => (List.finRange Θ.arity).all fun j =>
    match declaredUniverse Θ.raw i, declaredUniverse Θ.raw j with
    | some w, some w' => decide (S.R.cumulative w w') || decide (S.R.cumulative w' w)
    | _, _ => true

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
theorem chain_of_B {Θ : Context S.R} (h : chainB Θ = true) : Chain Θ := by
  intro i j w w' hi hj
  have hij := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  unfold declaredUniverse at hij
  rw [hi, hj] at hij
  simp only [headOf, Bool.or_eq_true, decide_eq_true_eq] at hij
  exact hij

/-- The left unknown of an equation, read off its codes. -/
def leftOf {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (Fin Θ.arity) := varOf e.1.2.code

/-- **Membership in the fragment of flex-rigid stores, decided.** -/
def inFlexRigidB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  allUniverseDeclsB Θ && chainB Θ && problem.all (fun e => (readFlexArrow e).isSome) &&
    problem.all (fun e => (arrowHeads e.2.2.code).all fun h => (choices.typing h).isSome) &&
    (problem.map leftOf).Nodup

theorem inFlexRigid_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inFlexRigidB choices problem = true) : InFlexRigid choices problem := by
  simp only [inFlexRigidB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hAll, hChain⟩, hShapes⟩, hHeads⟩, hNodup⟩ := h
  refine ⟨allUniverseDecls_of_B hAll, chain_of_B hChain, fun e member => ?_, fun e member h hh => ?_, ?_⟩
  · have he := List.all_eq_true.mp hShapes e member
    cases hd : readFlexArrow e with
    | none => rw [hd] at he; cases he
    | some d => exact ⟨viewOfArrow hd⟩
  · exact List.all_eq_true.mp (List.all_eq_true.mp hHeads e member) h hh
  · have pairwise := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hNodup)
    refine pairwise.imp ?_
    intro e₁ e₂ different v₁ v₂ same
    apply different
    unfold leftOf
    rw [v₁.side_left, v₂.side_left, same]

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
