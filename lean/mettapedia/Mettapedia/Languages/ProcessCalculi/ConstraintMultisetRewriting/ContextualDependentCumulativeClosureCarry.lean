import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureAfterSpine

/-!
# Closure of the cumulative round: updates that survive later declarations

R86's in-place rule, R107's inversion in place and the reorder rule solve a metavariable below later declarations: they
strengthen part of the store past the newest declaration, solve there, and carry the outcome back
(`ContextualDependentInPlace.carry`), lifting the answer past the declaration (`Update.lift`). Stability under
prefixes (`StableKeeps`) does not survive such a lift, since the carried prefixes mention the later declaration. This
file sets up an invariant that does.

* **Good answers** (`Good`): the composition closure of answers that reduce to pattern answers. It is closed under
  lifting past a metavariable (`Good.lift`), at the level of raw substitutions, and good answers keep closed normal
  Miller reducts (`Good.closedPreserving`), so they keep the permuted class (`PermutedMiller.applyStore_good`).
* **The permuted class reads codes only**: two stores whose code multisets agree are in the class together
  (`PermutedMiller.of_codes`).
* **Shaped updates** (`Shape`): the instantiated store is, up to codes and order, the residual store followed by
  equations that hold everywhere, under a good answer. A shaped update is stable (`Shape.stable`), and shapes compose
  (`Shape.then`), survive keeping equations in front (`Shape.keepLeft`), rephrasing along a store with the same codes
  (`Shape.rephrase`) and lifting past a declaration (`Shape.lift`). Drops under reducing answers are shaped
  (`shape_of_drop`), and so are reindexings of the whole store (`shape_of_reindex`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentDynamicFragment
open ContextualDependentExecutableJoin ContextualDependentClosure ContextualDependentHereditary

/-! ## Good answers -/

section Good

variable {Head : Type} {R : Rules Head}

/-- **A pattern answer past one more metavariable**: the new variable is renamed to itself and stays flexible. -/
def patternLiftMeta {n m : Nat} {σ : Sub Head n m}
    (answer : PatternAnswer R (bodyFlexible (o := n) 0) (bodyFlexible (o := m) 0) σ) :
    PatternAnswer R (bodyFlexible (o := n + 1) 0) (bodyFlexible (o := m + 1) 0) (liftSub σ) where
  target := answer.target.succ
  flexibleTarget := rfl
  rename i := Fin.cases (motive := fun i => i ≠ answer.target.succ → Fin (m + 1)) (fun _ => 0)
    (fun j hj => (answer.rename j (fun h => hj (congrArg Fin.succ h))).succ) i
  injective := by
    intro i j hi hj same
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
    · rfl
    · exact absurd same (Fin.succ_ne_zero _).symm
    · exact absurd same (Fin.succ_ne_zero _)
    · exact congrArg Fin.succ (answer.injective i j _ _ (Fin.succ_injective _ same))
  respects := fun _ _ => rfl
  others := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rfl
    · change Presentation.rename wk (σ i) = _
      rw [answer.others i (fun h => hi (congrArg Fin.succ h))]
      rfl
  outerArity := answer.outerArity
  outer := fun j => (answer.outer j).succ
  outerInjective := fun _ _ same => answer.outerInjective (Fin.succ_injective _ same)
  outerFlexible := fun _ => rfl
  value := answer.value
  solution := by
    change Presentation.rename wk (σ answer.target) = _
    rw [answer.solution, rename_comp]
    rfl
  valueMiller := answer.valueMiller
  valueNormal := answer.valueNormal

theorem ReducingAnswer.liftMeta {n m : Nat} {σ : Sub Head n m} (answer : ReducingAnswer R σ) :
    ReducingAnswer R (liftSub σ) := by
  obtain ⟨σ', reduces, ⟨pattern⟩⟩ := answer
  refine ⟨liftSub σ', fun i => ?_, ⟨patternLiftMeta pattern⟩⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .refl
  · exact star_rename (R := R) wk (reduces j)

/-- **Good answers**: the composition closure of answers that reduce to pattern answers. -/
inductive Good (R : Rules Head) : {n m : Nat} → Sub Head n m → Prop
  | reducing {n m : Nat} {σ : Sub Head n m} : ReducingAnswer R σ → Good R σ
  | comp {n m k : Nat} {tau : Sub Head m k} {sigma : Sub Head n m} : Good R tau → Good R sigma →
      Good R (subComp tau sigma)

/-- **Good answers survive lifting past a metavariable.** -/
theorem Good.lift {n m : Nat} {σ : Sub Head n m} (good : Good R σ) : Good R (liftSub σ) := by
  induction good with
  | reducing answer => exact .reducing answer.liftMeta
  | comp _ _ ihTau ihSigma =>
      rw [← liftSub_subComp]
      exact .comp ihTau ihSigma

/-- An answer keeps closed normal Miller reducts. -/
def ClosedPreserving (R : Rules Head) {n m : Nat} (σ : Sub Head n m) : Prop :=
  ∀ code : Tm Head n, MarkedReduct R (fun _ => true) code → MarkedReduct R (fun _ => true) (subst σ code)

variable (empty : R.computation = RootComputation.empty)
include empty

theorem ReducingAnswer.closedPreserving {n m : Nat} {σ : Sub Head n m} (answer : ReducingAnswer R σ) :
    ClosedPreserving R σ := by
  obtain ⟨σ', reduces, ⟨pattern⟩⟩ := answer
  intro code closed
  obtain ⟨N, toN, normalN, millerN⟩ := closed
  obtain ⟨N', toN', normalN', millerN'⟩ := answered_side_miller empty pattern 0 (code := code)
    (fun opened toOpened normalOpened => all_miller_of_one empty ⟨N, toN, normalN, millerN⟩ opened toOpened
      normalOpened)
    ⟨N, toN, normalN⟩
  exact ⟨N', (star_substitute reduces code).trans toN', normalN', millerN'⟩

/-- **Good answers keep closed normal Miller reducts.** -/
theorem Good.closedPreserving {n m : Nat} {σ : Sub Head n m} (good : Good R σ) : ClosedPreserving R σ := by
  induction good with
  | reducing answer => exact answer.closedPreserving empty
  | comp _ _ ihTau ihSigma =>
      intro code closed
      rw [← subst_subComp]
      exact ihTau _ (ihSigma code closed)

end Good

/-! ## The permuted class reads codes only -/

section Codes

theorem perm_lift_map {α β : Type} (f : α → β) :
    ∀ (L S : List α), (L.map f).Perm (S.map f) → ∃ L' : List α, L'.Perm S ∧ L'.map f = L.map f
  | [], S, perm => by
      have empty : S = [] := List.map_eq_nil_iff.mp perm.nil_eq.symm
      subst empty
      exact ⟨[], .refl _, rfl⟩
  | x :: L, S, perm => by
      have member : f x ∈ S.map f := perm.subset List.mem_cons_self
      obtain ⟨y, yMember, same⟩ := List.mem_map.mp member
      obtain ⟨A, C, rfl⟩ := List.append_of_mem yMember
      have middle : ((A ++ y :: C).map f).Perm (f y :: (A ++ C).map f) := by
        simp
      rw [same] at middle
      have rest : (L.map f).Perm ((A ++ C).map f) := (perm.trans middle).cons_inv
      obtain ⟨L', perm', mapped⟩ := perm_lift_map f L (A ++ C) rest
      exact ⟨y :: L', (perm'.cons y).trans List.perm_middle.symm, by simp [mapped, same]⟩

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem models_of_codes {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) :
    ∀ (store store' : EquationStore (TotalTerm Θ)), store.map codePiece = store'.map codePiece →
      ((frames S.levels).Models σ store ↔ (frames S.levels).Models σ store')
  | [], [], _ => Iff.rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | equation :: rest, equation' :: rest', same => by
      simp only [List.map_cons, List.cons.injEq] at same
      rw [ContextualDependentInPlace.models_cons, ContextualDependentInPlace.models_cons,
        models_of_codes σ rest rest' same.2]
      have codes := same.1
      simp only [codePiece, ContextualDependentSpinesMany.Piece.mk.injEq] at codes
      rw [ContextualDependentInPlace.solves_of_codes σ codes.1 codes.2.1 codes.2.2.1 codes.2.2.2]

variable (rigid : ∀ name, S.roles name = .rigid) (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R)
include rigid sn

theorem fragmentSidesMiller_of_codes {Θ : Context S.R} {equation equation' : Equation (TotalTerm Θ)}
    (left : equation.1.2.code = equation'.1.2.code) (right : equation.2.2.code = equation'.2.2.code)
    (sides : FragmentSidesMiller equation) : FragmentSidesMiller equation' := by
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn sides
  rw [left] at leftReduct
  rw [right] at rightReduct
  exact sides_of_reducts (computation_empty rigid) leftReduct rightReduct

theorem StratifiedMiller.of_codes {Θ : Context S.R} {ordered ordered' : EquationStore (TotalTerm Θ)}
    (codes : ordered'.map codePiece = ordered.map codePiece) (stratified : StratifiedMiller S.levels ordered) :
    StratifiedMiller S.levels ordered' := by
  intro before' after' equation' split
  rw [split, List.map_append, List.map_cons] at codes
  obtain ⟨before, rest, rfl, beforeCodes, restCodes⟩ := List.map_eq_append_iff.mp codes.symm
  obtain ⟨equation, after, rfl, equationCode, _⟩ := List.map_eq_cons_iff.mp restCodes
  obtain ⟨sides, annotations⟩ := stratified before after equation rfl
  simp only [codePiece, ContextualDependentSpinesMany.Piece.mk.injEq] at equationCode
  refine ⟨fragmentSidesMiller_of_codes rigid sn equationCode.2.1 equationCode.2.2.2 sides, fun σ solved => ?_⟩
  have held := annotations σ ((models_of_codes σ before before' beforeCodes).mpr solved)
  rw [← equationCode.1, ← equationCode.2.2.1]
  exact held

/-- **Two stores with the same codes, in any order, are in the permuted class together.** -/
theorem PermutedMiller.of_codes {Θ : Context S.R} {store store' : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels store) (codes : (store.map codePiece).Perm (store'.map codePiece)) :
    PermutedMiller S.levels store' := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  obtain ⟨ordered', perm', same⟩ := perm_lift_map codePiece ordered store' ((perm.map codePiece).trans codes)
  exact ⟨ordered', perm', StratifiedMiller.of_codes rigid sn same stratified⟩

/-- **A good answer keeps the permuted class.** -/
theorem PermutedMiller.applyStore_good {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (good : Good S.R σ.substitution)
    {store : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller S.levels store) :
    PermutedMiller S.levels ((frames S.levels).applyStore σ store) := by
  have empty := computation_empty rigid
  refine PermutedMiller.applyStore_of_sides σ permuted fun equation member => ?_
  obtain ⟨leftReduct, rightReduct⟩ := side_reduct rigid sn (permuted.sides_of_mem member)
  exact sides_of_reducts empty (good.closedPreserving empty _ leftReduct) (good.closedPreserving empty _ rightReduct)

omit rigid sn in
/-- Dropping equations that hold everywhere from the end of a store keeps the permuted class. -/
theorem PermutedMiller.drop_valid_suffix {Θ : Context S.R} {front : EquationStore (TotalTerm Θ)} :
    ∀ (valid : EquationStore (TotalTerm Θ)),
      (∀ v ∈ valid, ∀ {Δ : Context S.R} (τ : Δ ⟶ Θ), (frames S.levels).Solves τ v) →
      PermutedMiller S.levels (front ++ valid) → PermutedMiller S.levels front
  | [], _, permuted => by simpa using permuted
  | v :: rest, holds, permuted =>
      PermutedMiller.drop_valid_suffix rest (fun w member => holds w (List.mem_cons_of_mem _ member))
        (PermutedMiller.drop_valid (fun τ => holds v List.mem_cons_self τ) permuted)

end Codes

/-! ## Shaped updates -/

section Shape

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem codes_applyStore {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (store : EquationStore (TotalTerm Θ)) :
    ((frames S.levels).applyStore σ store).map codePiece =
      (store.map codePiece).map (ContextualDependentSpinesMany.Piece.subst σ.substitution) := by
  simp only [Interface.Frames.applyStore, List.map_map]
  rfl

theorem perm_applyStore {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {store store' : EquationStore (TotalTerm Θ)}
    (codes : (store.map codePiece).Perm (store'.map codePiece)) :
    (((frames S.levels).applyStore σ store).map codePiece).Perm
      (((frames S.levels).applyStore σ store').map codePiece) := by
  rw [codes_applyStore, codes_applyStore]
  exact codes.map _

theorem solves_act {Θ Δ Δ' : Context S.R} (σ : Δ ⟶ Θ) (τ : Δ' ⟶ Δ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves τ (equation.1.reindex σ, equation.2.reindex σ) ↔
      (frames S.levels).Solves (τ ≫ σ) equation := by
  have both := Frames.models_applyStore (X := frames S.levels) σ τ [equation]
  exact (models_singleton τ _).symm.trans (both.trans (models_singleton _ equation))

/-- **A shaped update**: under a good answer, the instantiated store is, up to codes and order, the residual store
followed by equations that hold everywhere. -/
def Shape {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (update : Update S.levels problem) : Prop :=
  ∃ valid : EquationStore (TotalTerm update.target),
    (((frames S.levels).applyStore update.answer problem).map codePiece).Perm
      ((update.remaining ++ valid).map codePiece) ∧
    (∀ v ∈ valid, ∀ {Δ : Context S.R} (τ : Δ ⟶ update.target), (frames S.levels).Solves τ v) ∧
    Good S.R update.answer.substitution

/-- **A shaped update is stable.** -/
theorem Shape.stable (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem} (shape : Shape update) :
    StableKeeps update := by
  intro before permuted
  obtain ⟨valid, codes, holds, good⟩ := shape
  have applied := PermutedMiller.applyStore_good rigid sn update.answer good permuted
  have split : (frames S.levels).applyStore update.answer (before ++ problem) =
      (frames S.levels).applyStore update.answer before ++ (frames S.levels).applyStore update.answer problem := by
    simp [Interface.Frames.applyStore]
  rw [split] at applied
  have moved : PermutedMiller S.levels
      ((frames S.levels).applyStore update.answer before ++ (update.remaining ++ valid)) :=
    PermutedMiller.of_codes rigid sn applied (by
      rw [List.map_append, List.map_append]
      exact codes.append_left _)
  exact PermutedMiller.drop_valid_suffix valid holds (by simpa only [List.append_assoc] using moved)

theorem Shape.then {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {first : Update S.levels problem}
    {second : Update S.levels first.remaining} (shapeFirst : Shape first) (shapeSecond : Shape second) :
    Shape (first.then second) := by
  obtain ⟨valid₁, codes₁, holds₁, good₁⟩ := shapeFirst
  obtain ⟨valid₂, codes₂, holds₂, good₂⟩ := shapeSecond
  refine ⟨valid₂ ++ (frames S.levels).applyStore second.answer valid₁, ?_, ?_, .comp good₂ good₁⟩
  · change (((frames S.levels).applyStore (second.answer ≫ first.answer) problem).map codePiece).Perm
      ((second.remaining ++ (valid₂ ++ (frames S.levels).applyStore second.answer valid₁)).map codePiece)
    rw [← applyStore_comp]
    refine (perm_applyStore second.answer codes₁).trans ?_
    have split : (frames S.levels).applyStore second.answer (first.remaining ++ valid₁) =
        (frames S.levels).applyStore second.answer first.remaining ++
          (frames S.levels).applyStore second.answer valid₁ := by
      simp [Interface.Frames.applyStore]
    rw [split, List.map_append, ← List.append_assoc, List.map_append]
    exact codes₂.append_right _
  · intro v member Δ τ
    rcases List.mem_append.mp member with inSecond | inFirst
    · exact holds₂ v inSecond τ
    · obtain ⟨w, wMember, rfl⟩ := List.mem_map.mp inFirst
      exact (solves_act second.answer τ w).mpr (holds₁ w wMember _)

theorem Shape.keepLeft {Θ : Context S.R} {rest : EquationStore (TotalTerm Θ)} (front : EquationStore (TotalTerm Θ))
    {update : Update S.levels rest} (shape : Shape update) : Shape (update.keepLeft front) := by
  obtain ⟨valid, codes, holds, good⟩ := shape
  refine ⟨valid, ?_, holds, good⟩
  change (((frames S.levels).applyStore update.answer (front ++ rest)).map codePiece).Perm
    ((((frames S.levels).applyStore update.answer front ++ update.remaining) ++ valid).map codePiece)
  have split : (frames S.levels).applyStore update.answer (front ++ rest) =
      (frames S.levels).applyStore update.answer front ++ (frames S.levels).applyStore update.answer rest := by
    simp [Interface.Frames.applyStore]
  rw [split, List.map_append, List.append_assoc, List.map_append]
  exact codes.append_left _

theorem Shape.rephrase {Θ : Context S.R} {source target : EquationStore (TotalTerm Θ)}
    {update : Update S.levels target} (same : (frames S.levels).Equivalent source target)
    (codes : (source.map codePiece).Perm (target.map codePiece)) (shape : Shape update) :
    Shape (update.rephrase same) := by
  obtain ⟨valid, codes', holds, good⟩ := shape
  exact ⟨valid, (perm_applyStore update.answer codes).trans codes', holds, good⟩

theorem Shape.lift {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {update : Update S.levels problem}
    (type : TypeOver Γ) (shape : Shape update) : Shape (update.lift type) := by
  obtain ⟨valid, codes, holds, good⟩ := shape
  refine ⟨(frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) valid, ?_, ?_,
    good.lift⟩
  · change (((frames S.levels).applyStore (rawLift update.answer type)
        ((frames S.levels).applyStore (projectionHom Γ type) problem)).map codePiece).Perm
      (((frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) update.remaining ++
        (frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) valid).map codePiece)
    rw [applyStore_comp, lift_projection, ← applyStore_comp]
    refine (perm_applyStore _ codes).trans ?_
    have split : (frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer))
          (update.remaining ++ valid) =
        (frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) update.remaining ++
          (frames S.levels).applyStore (projectionHom update.target (type.reindex update.answer)) valid := by
      simp [Interface.Frames.applyStore]
    rw [split]
  · intro v member Δ τ
    obtain ⟨w, wMember, rfl⟩ := List.mem_map.mp member
    exact (solves_act _ τ w).mpr (holds w wMember _)

/-- **A drop under a reducing answer is shaped.** -/
theorem shape_of_drop {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (drops : ReducingDrop problem update) : Shape update := by
  obtain ⟨first, rest, perm, remaining, valid, answer⟩ := drops
  refine ⟨[(first.1.reindex update.answer, first.2.reindex update.answer)], ?_, ?_, .reducing answer⟩
  · rw [remaining]
    have moved : (((frames S.levels).applyStore update.answer problem).map codePiece).Perm
        (((frames S.levels).applyStore update.answer (first :: rest)).map codePiece) :=
      ((perm.symm.map _).map codePiece)
    refine moved.trans ?_
    simp only [Interface.Frames.applyStore, List.map_cons, List.map_append, List.map_nil]
    exact (List.perm_append_singleton _ _).symm
  · intro v member Δ τ
    rw [List.mem_singleton.mp member]
    exact valid τ

/-- **A reindexing of the whole store along a reducing answer is shaped.** -/
theorem shape_of_reindex {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (remaining : update.remaining = (frames S.levels).applyStore update.answer problem)
    (answer : ReducingAnswer S.R update.answer.substitution) : Shape update :=
  ⟨[], by rw [remaining, List.append_nil], (fun _ member => by cases member), Good.reducing answer⟩

end Shape

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
