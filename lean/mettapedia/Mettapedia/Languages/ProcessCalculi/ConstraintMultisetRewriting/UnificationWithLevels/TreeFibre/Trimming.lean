import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.StrictInitiality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRefutation

/-!
# Deleting solved unknowns: principal answers become initial

The rules of the tree's fibre solve unknowns in place: the answer's telescope keeps every unknown, solved or not, so
a solved unknown is a free choice of every factor and the answer is not the initial solution
(`level_answer_not_initial`). Deleting the unknowns the answer does not fix repairs this.

* **Telescopes of closed families from a list** (`famTeleOf`, `lookup_famTeleOf`, `famTeleOf_formed`).
* **The trimmed telescope** keeps, in order, the unknowns the answer fixes (`keptOf`); `trimIn` reads each kept
  unknown back in the full telescope, and `trimOut` sends each kept unknown to itself and each deleted one to an
  inhabitant of its family.
* **Trimming theorem** (`initial_of_trimmed`): a principal answer on telescopes of universe families of one arity,
  whose image mentions only unknowns it fixes, and whose fixed unknowns keep their domains and lie below their
  declarations, becomes the initial solution once composed with `trimOut`: the composite with `trimIn` gives the
  answer back (`trim_back`), so it is principal, and it is covered (`initial_of_covered`).
* **Control** (`level_trimmed_initial`): the greatest-lower-bound answer on two level variables, not initial as it is,
  is initial after `X` is deleted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Telescopes of closed families from a list -/

section Lists

/-- The telescope declaring, from the last to the first, the families `view k` for `k` in `ks`. -/
def famTeleOf {n : Nat} (view : Fin n → List Head × Head) : (ks : List (Fin n)) → Ctx Head ks.length
  | [] => .nil
  | k :: rest => .snoc (famTeleOf view rest) (famCode (view k).1 (view k).2)

theorem lookup_famTeleOf {n : Nat} (view : Fin n → List Head × Head) :
    ∀ (ks : List (Fin n)) (k : Fin ks.length),
      Ctx.lookup (famTeleOf view ks) k = famCode (view (ks.get k)).1 (view (ks.get k)).2
  | [], k => k.elim0
  | j :: rest, k => by
      cases k using Fin.cases with
      | zero =>
          simp only [famTeleOf, Ctx.lookup_snoc_zero, famCode_rename]
          rfl
      | succ k =>
          simp only [famTeleOf, Ctx.lookup_snoc_succ, lookup_famTeleOf view rest k, famCode_rename]
          rfl

variable {S : Setting Head L}

theorem famTeleOf_formed {n : Nat} (view : Fin n → List Head × Head)
    (universes : ∀ j, AllUniverses S.R (view j).1 ∧ S.R.isUniverse (view j).2) :
    ∀ ks : List (Fin n), CtxFormed S.R (famTeleOf view ks)
  | [] => .nil
  | k :: rest => (famTeleOf_formed view universes rest).snoc
      (famCode_isType (view k).1 (universes k).1 (universes k).2 (famTeleOf_formed view universes rest))

end Lists

/-! ## The trimmed telescope and its two morphisms -/

section Trim

variable {S : Setting Head L} [DecidableEq Head]

/-- The unknowns an answer fixes, in order. -/
def keptOf {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (same : Δ.arity = Θ.arity) : List (Fin Δ.arity) :=
  (List.finRange Δ.arity).filter fun j => decide (σ.substitution (Fin.cast same j) = .var j)

theorem keptOf_nodup {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (same : Δ.arity = Θ.arity) : (keptOf σ same).Nodup :=
  (List.nodup_finRange _).filter _

theorem mem_keptOf {Δ Θ : Context S.R} (σ : Δ ⟶ Θ) (same : Δ.arity = Θ.arity) (j : Fin Δ.arity) :
    j ∈ keptOf σ same ↔ σ.substitution (Fin.cast same j) = .var j := by
  simp [keptOf, List.mem_filter, List.mem_finRange]

variable {Δ : Context S.R} (view : Fin Δ.arity → List Head × Head)
  (declared : ∀ j, Ctx.lookup Δ.raw j = famCode (view j).1 (view j).2)
  (universes : ∀ j, AllUniverses S.R (view j).1 ∧ S.R.isUniverse (view j).2)

/-- **The trimmed telescope**: the kept unknowns only. -/
abbrev trimCtx (ks : List (Fin Δ.arity)) : Context S.R where
  arity := ks.length
  raw := famTeleOf view ks
  formed := famTeleOf_formed view universes ks

/-- The kept unknown at a position, by its index in `ks`. -/
def keptAt (ks : List (Fin Δ.arity)) {j : Fin Δ.arity} (h : j ∈ ks) : Fin ks.length :=
  ⟨ks.idxOf j, List.idxOf_lt_length_of_mem h⟩

omit [DecidableEq Head] in
theorem get_keptAt (ks : List (Fin Δ.arity)) {j : Fin Δ.arity} (h : j ∈ ks) : ks.get (keptAt ks h) = j :=
  List.idxOf_get _

include declared in
/-- **Each kept unknown read back in the full telescope.** -/
def trimIn (ks : List (Fin Δ.arity)) : Δ ⟶ trimCtx view universes ks where
  substitution := fun k => .var (ks.get k)
  typed := by
    intro k
    have typed := Derivable.var (R := S.R) (Γ := Δ.raw) (ks.get k)
    rw [declared] at typed
    have look : Ctx.lookup (famTeleOf view ks) k = famCode (view (ks.get k)).1 (view (ks.get k)).2 :=
      lookup_famTeleOf view ks k
    change Typed S.R Δ.raw (.var (ks.get k)) (Presentation.subst _ (Ctx.lookup (famTeleOf view ks) k))
    rw [look, famCode_subst]
    exact typed

include declared in
/-- **Each kept unknown to itself, each deleted unknown to an inhabitant of its family.** -/
def trimOut (inh : Miller.Inhabitants S.R) (ks : List (Fin Δ.arity)) : trimCtx view universes ks ⟶ Δ where
  substitution := fun j => if h : j ∈ ks then .var (keptAt ks h)
    else Miller.lams (view j).1 (.head (inh.pick (view j).2))
  typed := by
    intro j
    have look := declared j
    change Typed S.R (famTeleOf view ks) _ (Presentation.subst _ (Ctx.lookup Δ.raw j))
    rw [look, famCode_subst]
    dsimp only
    by_cases h : j ∈ ks
    · rw [dif_pos h]
      have typed := Derivable.var (R := S.R) (Γ := famTeleOf view ks) (keptAt ks h)
      have at' : Ctx.lookup (famTeleOf view ks) (keptAt ks h) = famCode (view j).1 (view j).2 := by
        rw [lookup_famTeleOf, get_keptAt]
      rw [at'] at typed
      exact typed
    · rw [dif_neg h]
      exact Miller.lams_typed (view j).1 (famTeleOf_formed view universes ks) (universes j).1 (universes j).2
        (inh.typed (universes j).2 _)

omit [DecidableEq Head] in
/-- **Reading the kept unknowns back undoes the trimming on every code that mentions kept unknowns only.** -/
theorem trim_back (inh : Miller.Inhabitants S.R) (ks : List (Fin Δ.arity)) (code : Tm Head Δ.arity)
    (kept : ∀ j ∈ code.support, j ∈ ks) :
    Presentation.subst (trimIn view declared universes ks).substitution
        (Presentation.subst (trimOut view declared universes inh ks).substitution code) = code := by
  rw [subst_comp]
  rw [ContextualDependentGeneralPattern.subst_eq_of_support code _ ids (fun j member => by
    have inKs := kept j member
    change Presentation.subst _ (if h : j ∈ ks then Tm.var (keptAt ks h) else _) = _
    rw [dif_pos inKs]
    change Tm.var (ks.get (keptAt ks inKs)) = Tm.var j
    rw [get_keptAt])]
  exact subst_ids code

end Trim

/-! ## The trimming theorem -/

section Theorem

variable {S : Setting Head L} [DecidableEq Head]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (inh : Miller.Inhabitants S.R)

include facts roots heads algebra rigid complete in
/-- **Deleting the unknowns an answer does not fix makes a principal answer the initial solution**, when its image
mentions only unknowns it fixes, and each fixed unknown is declared with the same domains below its declaration in
the store's telescope. -/
theorem initial_of_trimmed {Δ Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {σ : Δ ⟶ Θ}
    (principal : (frames S.levels).Principal problem σ) (same : Δ.arity = Θ.arity)
    (view : Fin Δ.arity → List Head × Head) (declared : ∀ j, Ctx.lookup Δ.raw j = famCode (view j).1 (view j).2)
    (universes : ∀ j, AllUniverses S.R (view j).1 ∧ S.R.isUniverse (view j).2)
    (fixedSupport : ∀ (i : Fin Θ.arity) (j : Fin Δ.arity), j ∈ (σ.substitution i).support →
      σ.substitution (Fin.cast same j) = .var j)
    (lowered : ∀ j : Fin Δ.arity, σ.substitution (Fin.cast same j) = .var j → ∃ c',
      Ctx.lookup Θ.raw (Fin.cast same j) = famCode (view j).1 c' ∧ S.R.isUniverse c' ∧
        S.R.cumulative (view j).2 c') :
    InitialSolution (frames S.levels) problem
      (trimOut view declared universes inh (keptOf σ same) ≫ σ) := by
  have memKs := mem_keptOf σ same
  have back : trimIn view declared universes (keptOf σ same) ≫
      (trimOut view declared universes inh (keptOf σ same) ≫ σ) = σ := by
    apply Hom.ext
    funext i
    exact trim_back view declared universes inh (keptOf σ same) (σ.substitution i)
      (fun j member => (memKs j).mpr (fixedSupport i j member))
  refine initial_of_covered facts roots heads algebra rigid complete ⟨?_, ?_⟩ ?_
  · exact Frames.models_comp principal.sound _
  · intro b f solved
    obtain ⟨r, fr⟩ := principal.factors b f solved
    refine ⟨r ≫ trimIn view declared universes (keptOf σ same), fun t => ?_⟩
    have eq : (frames S.levels).comp (r ≫ trimIn view declared universes (keptOf σ same))
        (trimOut view declared universes inh (keptOf σ same) ≫ σ) = (frames S.levels).comp r σ := by
      change (r ≫ trimIn view declared universes (keptOf σ same)) ≫
        (trimOut view declared universes inh (keptOf σ same) ≫ σ) = r ≫ σ
      rw [Category.assoc, back]
    rw [eq]
    exact fr t
  · intro k
    have inKs : (keptOf σ same).get k ∈ keptOf σ same := List.get_mem _ k
    have fixed := (memKs _).mp inKs
    obtain ⟨c', dΘ, uc', below⟩ := lowered _ fixed
    refine ⟨Fin.cast same ((keptOf σ same).get k), (view ((keptOf σ same).get k)).1,
      (view ((keptOf σ same).get k)).2, c', ?_, lookup_famTeleOf view _ k, dΘ, (universes _).1, (universes _).2, uc',
      below⟩
    change Presentation.subst (trimOut view declared universes inh (keptOf σ same)).substitution
      (σ.substitution (Fin.cast same ((keptOf σ same).get k))) = .var k
    rw [fixed]
    change (if h : (keptOf σ same).get k ∈ keptOf σ same then Tm.var (keptAt _ h) else _) = _
    rw [dif_pos inKs]
    congr 1
    exact Fin.ext (List.get_idxOf (keptOf_nodup σ same) k)

end Theorem

/-! ## Control: the greatest-lower-bound answer, trimmed -/

namespace Controls

open ContextualDependentPatternFiring.Controls ContextualDependentSweep.Witnesses

/-- Both unknowns of the target are `U0 → U0`. -/
def levelView' : Fin levelTarget.arity → List Tower.Head × Tower.Head := fun _ => ([U0], U0)

theorem level_same : levelTarget.arity = ctxAB.arity := by decide +kernel

/-- **The answer fixes `Y` and mentions only `Y`.** -/
theorem level_fixedSupport : ∀ (i : Fin ctxAB.arity) (j : Fin levelTarget.arity),
    j ∈ (levelGlbUpdate.answer.substitution i).support →
      levelGlbUpdate.answer.substitution (Fin.cast level_same j) = .var j := by
  decide +kernel

/-- **`Y` is declared below its declaration in the store's telescope.** -/
theorem level_lowered : ∀ j : Fin levelTarget.arity,
    levelGlbUpdate.answer.substitution (Fin.cast level_same j) = .var j → ∃ c',
      Ctx.lookup ctxAB.raw (Fin.cast level_same j) = famCode (levelView' j).1 c' ∧ setting.R.isUniverse c' ∧
        setting.R.cumulative (levelView' j).2 c' := by
  intro j fixed
  have cases : j = targetY ∨ j = targetX := by
    rcases j with ⟨v, hv⟩
    have : v < 2 := hv
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases cases with rfl | rfl
  · exact ⟨Ub, by decide +kernel, by decide, by decide⟩
  · exact absurd fixed (by decide +kernel)

theorem levelView'_universes :
    ∀ j, AllUniverses setting.R (levelView' j).1 ∧ setting.R.isUniverse (levelView' j).2 :=
  fun _ => ⟨fun p member => by rw [List.mem_singleton.mp member]; decide, show setting.R.isUniverse U0 by decide⟩

/-- **The greatest-lower-bound answer on two level variables is the initial solution once `X` is deleted.** -/
theorem level_trimmed_initial :
    InitialSolution (frames setting.levels) levelStore
      (trimOut levelView' levelTarget_lookup levelView'_universes Miller.Controls.towerInh
        (keptOf levelGlbUpdate.answer level_same) ≫ levelGlbUpdate.answer) :=
  initial_of_trimmed TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Miller.Controls.towerInh level_glb_principal
    level_same levelView' levelTarget_lookup levelView'_universes level_fixedSupport level_lowered

/-- **Only `Y` is kept.** -/
theorem level_kept : keptOf levelGlbUpdate.answer level_same = [targetY] := by decide +kernel

end Controls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
