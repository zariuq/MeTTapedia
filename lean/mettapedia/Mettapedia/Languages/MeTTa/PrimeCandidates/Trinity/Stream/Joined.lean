import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream.AdmittedBySetSolution
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectShape
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextualPreservation

/-!
# The endless stream: the three faces joined

The stream of the numbers from `n` on is written `from n ⟶ scons n (from (suc n))`. Run as a
rule, every use of the equation produces a new call (`AdmittedBySetSolution`). A stream is read
through its observations, the element at a position, and those stop.

**Running.** A closed stream program is `from n` or a number before a program (`StreamExpr`).
The observation of position `k`, the program applied to the numeral `k`, runs by the steps of
the package to the numeral `StreamExpr.observe` gives (`StreamExpr.runs`): `from n` unfolds
once and moves one position on with the next number. `from n` at `k` reaches `n + k`
(`observe_numbersFrom`). The program itself reaches no term that takes no step
(`from_no_normal_form`). Every term it reaches is a running stream (`from_reaches_streamRun`):
`from` at a numeral, or a numeral before a running stream, so the term still contains a call
of `from`. A call of `from` at any argument is a root step (`from_step`), and that step lifts
from under a numeral placed in front, so every running stream takes a step
(`streamRun_steps`). The observation of a position does reach a numeral, and a numeral takes
no step (`observation_reaches_normal`, `numeral_no_step`). The same statement for a numeral
is false (`numeral_stops`).

**Three maps, built separately.** `typing` sends a program to its term, a stream (a function
from positions to numbers); `meaning` sends a typed term to its value in the set model;
`direct` sends a program to the function from positions whose value at `k` is the number the
observation of `k` runs to. The direct map uses neither the typed term nor the model.

**The triangle commutes by proof** (`meaning_typing`): every observation of the value of the
typed term is what the observation runs to (`StreamExpr.observation_value`), and two functions
from positions with the same values are one.

**The triangle is not exact** (`streamTriangle_loses`): `from n` and `scons n (from (suc n))`
are different programs with one stream (`observe_unfolded`). The set does not keep how far the
stream was unfolded when it was written.

Negative example: the written equation read as a loop of one node, the call coming back to the
same node with the change of argument forgotten, gives the first observation at every position
(`loopDirect`). For the stream from zero it holds zero at position one, where the typed term
means one, so these three maps form no triangle (`loop_disagrees`).

The further comparison with the Megalodon HOTG stream package is an explicit
profile integration in `PrimeComparisons.MegalodonHOTG.Stream`. It is not a
foundation imported by this candidate triangle.

Not here: the reading of the stream as a hyperset, the solution of a labelled graph with one
edge out of every node.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceApp traceLam traceApp_graph_beta)
open Mettapedia.Computability.ComputationalTrinity

universe u

/-! ## Programs and their observations -/

/-- **A closed stream program**: the stream of the numbers from `n` on, or a number before a
stream program. -/
inductive StreamExpr where
  | numbersFrom (n : Nat)
  | scons (a : Nat) (s : StreamExpr)
  deriving DecidableEq, Repr

/-- The term of a stream program. -/
def StreamExpr.toTerm : StreamExpr → CTm Tower.Head 0
  | .numbersFrom n => cfrom (cnumeral n)
  | .scons a s => cscons (cnumeral a) s.toTerm

/-- **What the observation of a position runs to**: `from n` unfolds once and moves one position
on with the next number; `scons a s` gives `a` at position zero and moves into `s` after
that. -/
def StreamExpr.observe : StreamExpr → Nat → Nat
  | .numbersFrom n, 0 => n
  | .numbersFrom n, k + 1 => StreamExpr.observe (.numbersFrom (n + 1)) k
  | .scons a _, 0 => a
  | .scons _ s, k + 1 => s.observe k

/-- The observations of `from n`: position `k` holds `n + k`. -/
theorem observe_numbersFrom : ∀ n k : Nat, (StreamExpr.numbersFrom n).observe k = n + k
  | n, 0 => rfl
  | n, k + 1 => by
      rw [StreamExpr.observe, observe_numbersFrom (n + 1) k]
      omega

/-- The written equation of `from` is a step of the package. -/
theorem from_step (x : CTm Tower.Head 0) :
    objectFrom.computation.step (cfrom x) (cscons x (cfrom (csuc x))) :=
  (StepsWithin.sum_right _ _).step ⟨fromEquation, List.mem_cons_self, fun _ => x, rfl, rfl⟩

/-- The first equation of `scons` is a step of the package. -/
theorem first_step (a s : CTm Tower.Head 0) :
    objectFrom.computation.step (.app (cscons a s) czero) a :=
  ((StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectScons _)).step
    ⟨sconsFirst, List.mem_cons_self, fun i => [s, a].getD i.val a, rfl, rfl⟩

/-- The second equation of `scons` is a step of the package. -/
theorem later_step (a s k : CTm Tower.Head 0) :
    objectFrom.computation.step (.app (cscons a s) (csuc k)) (.app s k) :=
  ((StepsWithin.sum_right objectChurch _).trans (StepsWithin.sum_left objectScons _)).step
    ⟨sconsLater, List.mem_cons_of_mem _ List.mem_cons_self, fun i => [k, s, a].getD i.val a,
      rfl, rfl⟩

/-- **Every observation runs to its number**, by the steps of the package: the written equation
produces a new call at every use, and reading the stream at a position still stops. -/
theorem StreamExpr.runs : ∀ (p : StreamExpr) (k : Nat),
    CReduces objectFrom (.app p.toTerm (cnumeral k)) (cnumeral (p.observe k))
  | .numbersFrom _, 0 =>
      Relation.ReflTransGen.head (.congAppFun (.root (from_step _)))
        (.single (.root (first_step _ _)))
  | .numbersFrom n, k + 1 =>
      Relation.ReflTransGen.head (.congAppFun (.root (from_step _)))
        (Relation.ReflTransGen.head (.root (later_step _ _ _))
          (StreamExpr.runs (.numbersFrom (n + 1)) k))
  | .scons _ _, 0 => .single (.root (first_step _ _))
  | .scons _ s, k + 1 =>
      Relation.ReflTransGen.head (.root (later_step _ _ _)) (s.runs k)

/-- A numeral is a number in the package with the stream. -/
theorem cnumeral_typed_from : ∀ k : Nat, CTyped objectFrom .nil (cnumeral k) cnum
  | 0 => ofObjectFrom czero_typed
  | k + 1 => csuc_typed_from (cnumeral_typed_from k)

/-- The term of every stream program is a stream. -/
theorem StreamExpr.toTerm_typed : ∀ p : StreamExpr, CTyped objectFrom .nil p.toTerm streamT
  | .numbersFrom n => cfrom_typed (cnumeral_typed_from n)
  | .scons a s => cscons_typed (cnumeral_typed_from a) s.toTerm_typed

/-! ## The program does not stop -/

section Forever

open Presentation.TypedEquality.Normalization

/-- **A numeral**: `zero`, or the successor of a numeral. -/
inductive Numeral : CTm Tower.Head 0 → Prop where
  | zero : Numeral czero
  | suc {t : CTm Tower.Head 0} : Numeral t → Numeral (csuc t)

/-- **A running stream**: `from` at a numeral, or a numeral before a running stream. -/
inductive StreamRun : CTm Tower.Head 0 → Prop where
  | call {t : CTm Tower.Head 0} : Numeral t → StreamRun (cfrom t)
  | front {a s : CTm Tower.Head 0} : Numeral a → StreamRun s → StreamRun (cscons a s)

/-- One step of `objectFrom`, anywhere in a closed term. -/
abbrev fromStep (t u : CTm Tower.Head 0) : Prop :=
  CStepCore objectFrom.computation objectRules.headEq t u

/-- Every closed numeral is `zero` or a tower of successors. -/
theorem cnumeral_numeral : ∀ k : Nat, Numeral (cnumeral k)
  | 0 => .zero
  | k + 1 => .suc (cnumeral_numeral k)

private theorem not_computes_rigid {c : DeclName} (mem : c ∉ nonrigidNames) :
    ∀ {arity : Nat} {inspect : InspectTree}, roles c ≠ .computes arity inspect := by
  intro _ _ eq
  rw [roles_of_not_mem mem] at eq
  cases eq

private theorem not_computes_zero :
    ∀ {arity : Nat} {inspect : InspectTree}, roles zeroN ≠ .computes arity inspect := by
  intro _ _ eq
  rw [roles_zero] at eq
  cases eq

private theorem not_computes_suc :
    ∀ {arity : Nat} {inspect : InspectTree}, roles sucN ≠ .computes arity inspect := by
  intro _ _ eq
  rw [roles_suc] at eq
  cases eq

private theorem no_church {t u : CTm Tower.Head 0} {c : DeclName} {args : List (Tm Tower.Head 0)}
    (erased : t.erase = appSpine (.const c) args)
    (notComp : ∀ {arity : Nat} {inspect : InspectTree}, roles c ≠ .computes arity inspect)
    (notHolds : c ≠ holdsN) (step : objectChurch.computation.step t u) : False := by
  rcases objectChurch.erase_step step with base | decoding
  · obtain ⟨_, arity, inspect, _, role, eq, _, _⟩ := shape.spine base
    obtain ⟨same, _⟩ := appSpine_const_injective (erased.symm.trans eq)
    exact notComp (arity := arity) (inspect := inspect) (same.symm ▸ role)
  · obtain ⟨_, eq⟩ := decoderComputation_headed programCodes.decoders decoding
    obtain ⟨same, _⟩ := appSpine_const_injective (erased.symm.trans eq)
    exact notHolds same

private theorem from_equation_head {l r : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step l r) : ∃ a, l.erase = .app (.const fromN) a := by
  rcases step with ⟨_, member, σ, rfl, _⟩
  obtain rfl : _ = fromEquation := List.mem_singleton.mp member
  dsimp [fromEquation] at σ
  refine ⟨(σ 0).erase, ?_⟩
  unfold fromEquation
  dsimp [cfrom, CTm.subst, CTm.erase]

private theorem from_equation_result {x r : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step (cfrom x) r) :
    r = cscons x (cfrom (csuc x)) := by
  rcases step with ⟨_, member, σ, left, right⟩
  obtain rfl : _ = fromEquation := List.mem_singleton.mp member
  unfold fromEquation at left right
  dsimp [cfrom, cscons, csuc, CTm.subst] at left right
  injection left with _ _ hx
  rw [← hx] at right
  exact right

private theorem scons_equation_head {l r : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step l r) :
    ∃ f a b, l.erase = .app (.app (.app (.const sconsN) f) a) b := by
  rcases step with ⟨_, member, σ, rfl, _⟩
  simp only [sconsEquations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · unfold sconsFirst
    dsimp [cscons, czero, CTm.subst, CTm.erase]
    exact ⟨_, _, _, rfl⟩
  · unfold sconsLater
    dsimp [cscons, csuc, CTm.subst, CTm.erase]
    exact ⟨_, _, _, rfl⟩

private theorem const_not_scons {c : DeclName} {u : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step (.const c) u) : False := by
  obtain ⟨_, _, _, eq⟩ := scons_equation_head step
  injection eq

private theorem const_not_from {c : DeclName} {u : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step (.const c) u) : False := by
  obtain ⟨_, eq⟩ := from_equation_head step
  injection eq

private theorem fromPackage_step {t u : CTm Tower.Head 0}
    (step : objectFrom.computation.step t u) :
    objectChurch.computation.step t u ∨
      (equationComputation sconsEquations).step t u ∨
      (equationComputation [fromEquation]).step t u := by
  rcases step with package | fromEq
  · rcases package with church | scons
    · exact Or.inl church
    · exact Or.inr (Or.inl scons)
  · exact Or.inr (Or.inr fromEq)

private theorem const_no_step {c : DeclName} {u : CTm Tower.Head 0}
    (notComp : ∀ {arity : Nat} {inspect : InspectTree}, roles c ≠ .computes arity inspect)
    (notHolds : c ≠ holdsN) : ¬ fromStep (.const c) u := by
  intro step
  cases step with
  | root s =>
      rcases fromPackage_step s with church | rest
      · exact no_church (args := []) rfl notComp notHolds church
      rcases rest with scons | fromEq
      · exact const_not_scons scons
      · exact const_not_from fromEq

private theorem suc_not_scons {t r : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step (csuc t) r) : False := by
  obtain ⟨_, _, _, eq⟩ := scons_equation_head step
  have erased : (csuc t).erase = Tm.app (Tm.const sucN) t.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads

private theorem suc_not_from {t r : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step (csuc t) r) : False := by
  obtain ⟨_, eq⟩ := from_equation_head step
  have erased : (csuc t).erase = Tm.app (Tm.const sucN) t.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads with _ same
  exact absurd same (by decide)

private theorem suc_not_root {t r : CTm Tower.Head 0}
    (step : objectFrom.computation.step (csuc t) r) : False := by
  rcases fromPackage_step step with church | rest
  · exact no_church (args := [t.erase]) rfl not_computes_suc (by decide) church
  rcases rest with scons | fromEq
  · exact suc_not_scons scons
  · exact suc_not_from fromEq

/-- **A numeral takes no step of the package.** -/
theorem numeral_no_step {t u : CTm Tower.Head 0} (num : Numeral t) : ¬ fromStep t u := by
  induction num generalizing u with
  | zero => exact const_no_step not_computes_zero (by decide)
  | suc _ ih =>
      intro step
      cases step with
      | root s => exact suc_not_root s
      | congAppFun inner => exact const_no_step not_computes_suc (by decide) inner
      | congAppArg inner => exact ih inner

private theorem cfrom_not_scons {x r : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step (cfrom x) r) : False := by
  obtain ⟨_, _, _, eq⟩ := scons_equation_head step
  have erased : (cfrom x).erase = Tm.app (Tm.const fromN) x.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads

private theorem call_root {x r : CTm Tower.Head 0}
    (step : objectFrom.computation.step (cfrom x) r) : r = cscons x (cfrom (csuc x)) := by
  rcases fromPackage_step step with church | rest
  · exact False.elim (no_church (args := [x.erase]) rfl (not_computes_rigid (by decide))
      (by decide) church)
  rcases rest with scons | fromEq
  · exact False.elim (cfrom_not_scons scons)
  · exact from_equation_result fromEq

private theorem call_step {x u : CTm Tower.Head 0} (num : Numeral x) (step : fromStep (cfrom x) u) :
    u = cscons x (cfrom (csuc x)) := by
  cases step with
  | root s => exact call_root s
  | congAppFun inner => exact False.elim (const_no_step (not_computes_rigid (by decide))
      (by decide) inner)
  | congAppArg inner => exact False.elim (numeral_no_step num inner)

private theorem partial_not_scons {a r : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step (CTm.app (.const sconsN) a) r) : False := by
  obtain ⟨_, _, _, eq⟩ := scons_equation_head step
  have erased : (CTm.app (.const sconsN) a).erase = Tm.app (Tm.const sconsN) a.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads

private theorem partial_not_from {a r : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step (CTm.app (.const sconsN) a) r) : False := by
  obtain ⟨_, eq⟩ := from_equation_head step
  have erased : (CTm.app (.const sconsN) a).erase = Tm.app (Tm.const sconsN) a.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads with _ same
  exact absurd same (by decide)

private theorem partial_no_step {a u : CTm Tower.Head 0} (num : Numeral a) :
    ¬ fromStep (CTm.app (.const sconsN) a) u := by
  intro step
  cases step with
  | root s =>
      rcases fromPackage_step s with church | rest
      · exact no_church (args := [a.erase]) rfl (not_computes_rigid (by decide)) (by decide) church
      rcases rest with scons | fromEq
      · exact partial_not_scons scons
      · exact partial_not_from fromEq
  | congAppFun inner => exact const_no_step (not_computes_rigid (by decide)) (by decide) inner
  | congAppArg inner => exact numeral_no_step num inner

private theorem front_not_scons {a s r : CTm Tower.Head 0}
    (step : (equationComputation sconsEquations).step (cscons a s) r) : False := by
  obtain ⟨_, _, _, eq⟩ := scons_equation_head step
  have erased : (cscons a s).erase = Tm.app (Tm.app (Tm.const sconsN) a.erase) s.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads with _ heads _
  injection heads

private theorem front_not_from {a s r : CTm Tower.Head 0}
    (step : (equationComputation [fromEquation]).step (cscons a s) r) : False := by
  obtain ⟨_, eq⟩ := from_equation_head step
  have erased : (cscons a s).erase = Tm.app (Tm.app (Tm.const sconsN) a.erase) s.erase := rfl
  rw [erased] at eq
  injection eq with _ heads _
  injection heads

private theorem front_not_root {a s r : CTm Tower.Head 0}
    (step : objectFrom.computation.step (cscons a s) r) : False := by
  rcases fromPackage_step step with church | rest
  · exact no_church (args := [a.erase, s.erase]) rfl (not_computes_rigid (by decide))
      (by decide) church
  rcases rest with scons | fromEq
  · exact front_not_scons scons
  · exact front_not_from fromEq

private theorem front_step {a s u : CTm Tower.Head 0} (num : Numeral a)
    (step : fromStep (cscons a s) u) : ∃ s', fromStep s s' ∧ u = cscons a s' := by
  cases step with
  | root s => exact False.elim (front_not_root s)
  | congAppFun inner => exact False.elim (partial_no_step num inner)
  | congAppArg inner => exact ⟨_, inner, rfl⟩

/-- **A running stream takes a step**, at the call of `from`. -/
theorem streamRun_steps {t : CTm Tower.Head 0} (run : StreamRun t) : ∃ u, fromStep t u := by
  induction run with
  | call _ => exact ⟨_, .root (from_step _)⟩
  | front _ _ ih =>
      obtain ⟨_, step⟩ := ih
      exact ⟨_, .congAppArg step⟩

/-- **A step of a running stream is a running stream**, so the call of `from` remains. -/
theorem streamRun_preserved {t u : CTm Tower.Head 0} (run : StreamRun t) (step : fromStep t u) :
    StreamRun u := by
  induction run generalizing u with
  | call num =>
      rw [call_step num step]
      exact .front num (.call (.suc num))
  | front num _ ih =>
      obtain ⟨_, step', rfl⟩ := front_step num step
      exact .front num (ih step')

/-- **A running stream reaches only running streams.** -/
theorem reaches_streamRun {t u : CTm Tower.Head 0} (run : StreamRun t)
    (reached : CReduces objectFrom t u) : StreamRun u := by
  induction reached with
  | refl => exact run
  | tail _ step ih => exact streamRun_preserved ih step

/-- **What `from n` reaches is a running stream.** -/
theorem from_reaches_streamRun (n : Nat) {u : CTm Tower.Head 0}
    (reached : CReduces objectFrom (cfrom (cnumeral n)) u) : StreamRun u :=
  reaches_streamRun (.call (cnumeral_numeral n)) reached

/-- **`from n` reaches no term that takes no step.** -/
theorem from_no_normal_form (n : Nat) {u : CTm Tower.Head 0}
    (reached : CReduces objectFrom (cfrom (cnumeral n)) u) : ∃ v, fromStep u v :=
  streamRun_steps (from_reaches_streamRun n reached)

/-- **An observation of `from n` reaches a numeral, and that numeral takes no step.** -/
theorem observation_reaches_normal (n k : Nat) :
    ∃ u, CReduces objectFrom (.app (cfrom (cnumeral n)) (cnumeral k)) u ∧
      ¬ ∃ v, fromStep u v := by
  refine ⟨cnumeral ((StreamExpr.numbersFrom n).observe k),
    StreamExpr.runs (StreamExpr.numbersFrom n) k, ?_⟩
  intro ⟨_, step⟩
  exact numeral_no_step (cnumeral_numeral _) step

/-- **The statement of `from_no_normal_form` is false for a numeral.** -/
theorem numeral_stops (k : Nat) :
    ¬ ∀ u, CReduces objectFrom (cnumeral k) u → ∃ v, fromStep u v := by
  intro endless
  obtain ⟨_, step⟩ := endless (cnumeral k) .refl
  exact numeral_no_step (cnumeral_numeral k) step

end Forever

/-! ## In the sets -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- A numeral means its number. -/
theorem cnumeral_value : ∀ k : Nat,
    ev (objHeads h) (fromConsts h) (cnumeral k) Fin.elim0 = numeral k
  | 0 => zero_value h (agrees_object h (fromConsts_agrees h))
  | k + 1 => by
      show traceApp (fromConsts h sucN)
        (ev (objHeads h) (fromConsts h) (cnumeral k) Fin.elim0) = _
      rw [cnumeral_value k,
        suc_value h (agrees_object h (fromConsts_agrees h)) (numeral_mem_omega _)]
      rfl

/-- The value of a stream program is a stream. -/
theorem StreamExpr.toTerm_mem : ∀ p : StreamExpr,
    ev (objHeads h) (fromConsts h) p.toTerm Fin.elim0 ∈ streams
  | .numbersFrom n => by
      show traceApp (fromConsts h fromN) (ev (objHeads h) (fromConsts h) (cnumeral n) Fin.elim0)
        ∈ streams
      rw [cnumeral_value h, show fromConsts h fromN = fromValue from Function.update_self _ _ _,
        fromValue_apply (numeral_mem_omega n)]
      exact fromStream_mem _
  | .scons a s => by
      show traceApp (traceApp (fromConsts h sconsN)
          (ev (objHeads h) (fromConsts h) (cnumeral a) Fin.elim0))
        (ev (objHeads h) (fromConsts h) s.toTerm Fin.elim0) ∈ streams
      rw [cnumeral_value h, scons_at h (fromConsts_agrees h),
        sconsValue_apply (numeral_mem_omega a) (s.toTerm_mem)]
      exact sconsStream_mem (numeral_mem_omega a) s.toTerm_mem

/-- **Every observation of the typed term's value is what the observation runs to.** -/
theorem StreamExpr.observation_value : ∀ (p : StreamExpr) (k : Nat),
    traceApp (ev (objHeads h) (fromConsts h) p.toTerm Fin.elim0) (numeral k) =
      numeral (p.observe k)
  | .numbersFrom n, k => by
      show traceApp (traceApp (fromConsts h fromN)
        (ev (objHeads h) (fromConsts h) (cnumeral n) Fin.elim0)) (numeral k) = _
      rw [cnumeral_value h, show fromConsts h fromN = fromValue from Function.update_self _ _ _,
        fromValue_apply (numeral_mem_omega n), fromStream_apply (numeral_mem_omega k),
        natOf_numeral, natOf_numeral, observe_numbersFrom]
  | .scons a s, k => by
      show traceApp (traceApp (traceApp (fromConsts h sconsN)
          (ev (objHeads h) (fromConsts h) (cnumeral a) Fin.elim0))
        (ev (objHeads h) (fromConsts h) s.toTerm Fin.elim0)) (numeral k) = _
      rw [cnumeral_value h, scons_at h (fromConsts_agrees h),
        sconsValue_apply (numeral_mem_omega a) (s.toTerm_mem h),
        sconsStream_apply (numeral_mem_omega k)]
      unfold sconsAt
      cases k with
      | zero => rw [natOf_numeral, if_pos rfl]; rfl
      | succ k =>
          rw [natOf_numeral, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel,
            s.observation_value k]
          rfl

end Model

/-! ## The triangle -/

/-- A closed term of the package that is a stream, with its typing. -/
abbrev TypedStream : Type := { t : CTm Tower.Head 0 // CTyped objectFrom .nil t streamT }

/-- **What runs is typed**: the term of a stream program, with the proof that it is a stream. -/
def typing (p : StreamExpr) : TypedStream := ⟨p.toTerm, p.toTerm_typed⟩

/-- **What is typed means a set**: the value of a typed term in the set model. -/
noncomputable def meaning (h : CofinalInaccessibles.{u}) (t : TypedStream) : ZFSet.{u} :=
  ev (objHeads h) (fromConsts h) t.1 Fin.elim0

/-- **What runs reaches a set**: the function from positions whose value at `k` is the number
the observation of position `k` runs to. Each observation stops. -/
noncomputable def direct (p : StreamExpr) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun x => numeral (p.observe (natOf x)))

/-- **The three ways to a set agree**: the stream the typed term means is the function of the
observations. -/
theorem meaning_typing (h : CofinalInaccessibles.{u}) (p : StreamExpr) :
    meaning h (typing p) = direct p :=
  tracePiSet_ext (p.toTerm_mem h) (traceLam_graph_mem fun _ _ => numeral_mem_omega _)
    fun x hx => by
      have point := p.observation_value h (natOf x)
      rw [numeral_natOf hx] at point
      rw [direct, traceApp_graph_beta _ hx]
      exact point

/-- **The triangle of the three faces of the endless stream.** -/
noncomputable def streamTriangle (h : CofinalInaccessibles.{u}) : Comparison.{0, 0, u + 1} Closed :=
  triangleOfThree
    (fun p : ULift.{u + 1} StreamExpr => (ULift.up (typing p.down) : ULift.{u + 1} TypedStream))
    (fun t => meaning h t.down) (fun p => direct p.down) fun p => meaning_typing h p.down

/-- One unfolding written out changes no observation. -/
theorem observe_unfolded (n : Nat) :
    ∀ k : Nat, (StreamExpr.scons n (.numbersFrom (n + 1))).observe k =
      (StreamExpr.numbersFrom n).observe k
  | 0 => rfl
  | _ + 1 => rfl

/-- **The triangle is not exact**: `from n` and `scons n (from (suc n))` are different programs
with one stream. -/
theorem streamTriangle_loses (h : CofinalInaccessibles.{u}) (n : Nat) :
    (streamTriangle h).LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := ⟨.numbersFrom n⟩)
    (right := ⟨.scons n (.numbersFrom (n + 1))⟩)
    (fun same => absurd (congrArg ULift.down same) (by simp))
    (show (direct (.numbersFrom n) : ZFSet.{u}) = direct (.scons n (.numbersFrom (n + 1))) by
      unfold direct
      simp only [observe_unfolded])

/-! ## A negative control -/

/-- **The equation read as a loop of one node**: the written equation
`from n ⟶ scons n (from (suc n))` with the change of argument forgotten, so that the call comes
back to the same node. Every position holds the first observation. -/
noncomputable def loopDirect (p : StreamExpr) : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun _ => numeral (p.observe 0))

/-- Negative example: **read as a loop of one node, the stream from zero holds zero at position
one, and the typed term means one there**, so the three maps form no triangle. -/
theorem loop_disagrees (h : CofinalInaccessibles.{u}) :
    ¬ ∀ p : StreamExpr, meaning h (typing p) = loopDirect p := by
  intro agree
  have atOne := congrArg (fun s => traceApp s (numeral 1)) (agree (.numbersFrom 0))
  rw [meaning, typing, StreamExpr.observation_value h, loopDirect,
    traceApp_graph_beta _ (numeral_mem_omega 1)] at atOne
  exact absurd (numeral_injective atOne) (by decide)

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Stream
