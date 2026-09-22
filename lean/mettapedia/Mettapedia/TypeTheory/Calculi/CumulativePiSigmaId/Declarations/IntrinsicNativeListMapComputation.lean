import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMaps
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mettapedia.GSLT.Core.GSLTConstructions

/-!
# Directed computation of the intrinsic List map

The existing map is a dependent-calculus program built from the actual List
eliminator. Here its beta/iota execution is proved on arbitrary finite
constructor spines, including open element terms. Computation and its OSLF
observation reuse the declared rules; no host `List.map` is a reduction rule.

This is a raw computation theorem, not a new typing or parsing authority.
The separate formation judgment remains required for logical use.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.IntrinsicNativeListMapComputation

open Presentation NativeIndexedFamilies IntrinsicMaps
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

variable {n m : Nat}

@[simp] private theorem subst_vars (term : Tower.Tm n) :
    subst (fun i => .var i) term = term := subst_ids term

private theorem fin_two (n : Nat) : (2 : Fin (n + 3)) =
    (0 : Fin (n + 1)).succ.succ := by
  apply Fin.ext
  change 2 % (n + 3) = 0 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)
private theorem fin_three (n : Nat) : (3 : Fin (n + 4)) =
    (0 : Fin (n + 1)).succ.succ.succ := by
  apply Fin.ext
  change 3 % (n + 4) = 0 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)
private theorem fin_four (n : Nat) : (4 : Fin (n + 5)) =
    (0 : Fin (n + 1)).succ.succ.succ.succ := by
  apply Fin.ext
  change 4 % (n + 5) = 0 + 1 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)
private theorem fin_five (n : Nat) : (5 : Fin (n + 6)) =
    (0 : Fin (n + 1)).succ.succ.succ.succ.succ := by
  apply Fin.ext
  change 5 % (n + 6) = 0 + 1 + 1 + 1 + 1 + 1
  exact Nat.mod_eq_of_lt (by omega)

/-- The executable beta/iota rules, at the chosen declaration level.  Native
universe-head equality is intentionally absent: it is a semantic conversion
service rather than a member of the finite computation inventory. -/
def reduction (level : LevelExpr) (n : Nat) : Mettapedia.GSLT.GSLT :=
  equalityGSLT (Tower.Tm n)
    (StepCore (listRulesAt level).computation (fun _ _ => False))

/-- The corresponding full native relation, when semantic universe-head
equality is required in addition to executable beta/iota computation. -/
def fullReduction (level : LevelExpr) (n : Nat) : Mettapedia.GSLT.GSLT :=
  equalityGSLT (Tower.Tm n)
    (StepCore (listRulesAt level).computation (listRulesAt level).headEq)

abbrev Reduces (level : LevelExpr) (left right : Tower.Tm n) :=
  (reduction level n).MultiStep left right

theorem Reduces.trans {level : LevelExpr} {a b c : Tower.Tm n}
    (first : Reduces level a b) (second : Reduces level b c) :
    Reduces level a c := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (reduction level n)
    (fun a b _ => ∀ c, Reduces level b c → Reduces level a c)
    (fun _ _ path => path)
    (fun {_ _ _} edge _ ih c path => .step edge (ih c path)) a b first c second

theorem Reduces.appFun {level : LevelExpr} {a b : Tower.Tm n}
    (path : Reduces level a b) (argument : Tower.Tm n) :
    Reduces level (.app a argument) (.app b argument) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (reduction level n)
    (fun a b _ => Reduces level (.app a argument) (.app b argument))
    (fun _ => .refl _) (fun {_ _ _} edge _ ih => .step (.congAppFun edge) ih) a b path

theorem Reduces.appArg {level : LevelExpr} {a b : Tower.Tm n}
    (path : Reduces level a b) (function : Tower.Tm n) :
    Reduces level (.app function a) (.app function b) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (reduction level n)
    (fun a b _ => Reduces level (.app function a) (.app function b))
    (fun _ => .refl _) (fun {_ _ _} edge _ ih => .step (.congAppArg edge) ih) a b path

theorem Reduces.substitute {level : LevelExpr} {a b : Tower.Tm n}
    (path : Reduces level a b) (sigma : Sub Tower.Head n m) :
    Reduces level (subst sigma a) (subst sigma b) := by
  refine @Mettapedia.GSLT.GSLT.MultiStep.rec (reduction level n)
    (fun a b _ => Reduces level (subst sigma a) (subst sigma b))
    (fun _ => .refl _) (fun {_ _ _} edge _ ih => .step (edge.substitute sigma) ih) a b path

theorem Reduces.beta (level : LevelExpr) (body : Tower.Tm (n + 1))
    (argument : Tower.Tm n) :
    Reduces level (.app (.lam body) argument) (inst0 argument body) :=
  .step (.betaPi body argument) (.refl _)

/-- A constructor spine of authored terms, without a semantic replacement
of the native List constructors. -/
def encode (element : Tower.Tm n) : List (Tower.Tm n) → Tower.Tm n
  | [] => Intrinsic.nilApp element
  | head :: tail => Intrinsic.consApp element head (encode element tail)

@[simp] theorem encode_subst (element : Tower.Tm n)
    (xs : List (Tower.Tm n)) (sigma : Sub Tower.Head n m) :
    subst sigma (encode element xs) =
      encode (subst sigma element) (xs.map (subst sigma)) := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp only [encode, List.map_cons, Intrinsic.consApp,
      subst, ih]

/-- The actual eliminator motive and recursive case after application of
the four map arguments. -/
def motive (target : Tower.Tm n) : Tower.Tm n :=
  .lam (Intrinsic.listApp (rename wk target))

def branch (target function : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (Intrinsic.consApp
    (rename (fun i => i.succ.succ.succ) target)
    (.app (rename (fun i => i.succ.succ.succ) function) (.var 2)) (.var 0))))

def mapped (source target function xs : Tower.Tm n) : Tower.Tm n :=
  Intrinsic.eliminateApp source (motive target) (Intrinsic.nilApp target)
    (branch target function) xs

def applyMap (source target function xs : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (liftClosed nativeMapTerm) source) target) function) xs

theorem branch_beta (level : LevelExpr) (target function head tail result : Tower.Tm n) :
    Reduces level (.app (.app (.app (branch target function) head) tail) result)
      (Intrinsic.consApp target (.app function head) result) := by
  unfold branch
  refine (Reduces.appFun (Reduces.appFun (Reduces.beta level _ head) tail) result).trans ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine (Reduces.appFun (Reduces.beta level _ tail) result).trans ?_
  dsimp [inst0, subst, subst0, liftSub]
  convert Reduces.beta level _ result using 1
  simp only [Intrinsic.consApp, inst0, subst, subst_rename]
  simp [subst0, liftSub, wk, subst, rename, fin_two,
    -Fin.succ_zero_eq_one, -Fin.succ_one_eq_two,
    -Fin.succ_zero_eq_one', -Fin.succ_one_eq_two']
  simp [subst_rename, subst0, rename]

theorem applyMap_beta (level : LevelExpr) (source target function xs : Tower.Tm n) :
    Reduces level (applyMap source target function xs) (mapped source target function xs) := by
  unfold applyMap nativeMapTerm liftClosed
  dsimp [rename]
  refine (Reduces.appFun (Reduces.appFun (Reduces.appFun
    (Reduces.beta level _ source) target) function) xs).trans ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine (Reduces.appFun (Reduces.appFun (Reduces.beta level _ target) function) xs).trans ?_
  dsimp [inst0, subst, subst0, liftSub]
  refine (Reduces.appFun (Reduces.beta level _ function) xs).trans ?_
  dsimp [inst0, subst, subst0, liftSub]
  convert Reduces.beta level _ xs using 1
  change mapped source target function xs =
    subst (subst0 xs)
      (subst (liftSub (subst0 function))
        (subst (liftSub (liftSub (subst0 target)))
          (subst (liftSub (liftSub (liftSub (subst0 source))))
            (rename (liftRen (liftRen (liftRen (liftRen Fin.elim0)))) nativeMapBody))))
  rw [Intrinsic.instantiateFour_eq_subst]
  simp [mapped, nativeMapBody, nativeMapMotive, nativeMapNilCase,
    nativeMapConsCase, motive, branch, Intrinsic.eliminateApp,
    Intrinsic.nilApp, Intrinsic.consApp, Intrinsic.listApp,
    Intrinsic.nilSchemaSubstitution, Intrinsic.nilCaseSchemaSubstitution,
    Intrinsic.motiveSchemaSubstitution, consSub, Fin.cases, subst, liftSub, wk,
    fin_two, fin_three, fin_four, fin_five,
    -Fin.succ_zero_eq_one, -Fin.succ_one_eq_two,
    -Fin.succ_zero_eq_one', -Fin.succ_one_eq_two']
  dsimp [Fin.induction, Intrinsic.elementSchemaSubstitution, consSub, Fin.cases]
  simp [Fin.induction.go, rename_comp, rename]

theorem mapped_nil (level : LevelExpr) (source target function : Tower.Tm n) :
    Reduces level (mapped source target function (Intrinsic.nilApp source))
      (Intrinsic.nilApp target) := by
  apply Mettapedia.GSLT.GSLT.MultiStep.step _ (.refl _)
  exact .root (.declared ⟨.nil _ _ _ _⟩)

theorem mapped_cons (level : LevelExpr) (source target function head tail : Tower.Tm n) :
    Reduces level (mapped source target function (Intrinsic.consApp source head tail))
      (Intrinsic.consApp target (.app function head) (mapped source target function tail)) := by
  refine .step (.root (.declared ⟨.cons _ _ _ _ _ _⟩)) ?_
  exact branch_beta level target function head tail (mapped source target function tail)

/-- Recursion follows the declared cons equation, followed by ordinary beta
steps. The mapped head is retained as an application, not evaluated by Lean. -/
theorem mapped_encode (level : LevelExpr) (source target function : Tower.Tm n)
    (xs : List (Tower.Tm n)) :
    Reduces level (mapped source target function (encode source xs))
      (encode target (xs.map (fun x => .app function x))) := by
  induction xs with
  | nil => exact mapped_nil level source target function
  | cons head tail ih =>
      exact (mapped_cons level source target function head (encode source tail)).trans
        (ih.appArg (.app (.app (.const Intrinsic.consName) target) (.app function head)))

theorem applyMap_encode (level : LevelExpr) (source target function : Tower.Tm n)
    (xs : List (Tower.Tm n)) :
    Reduces level (applyMap source target function (encode source xs))
      (encode target (xs.map (fun x => .app function x))) :=
  (applyMap_beta level source target function (encode source xs)).trans
    (mapped_encode level source target function xs)

theorem encode_pointwise (level : LevelExpr) (element : Tower.Tm n)
    (f g : Tower.Tm n → Tower.Tm n) (xs : List (Tower.Tm n))
    (pointwise : ∀ x ∈ xs, Reduces level (f x) (g x)) :
    Reduces level (encode element (xs.map f)) (encode element (xs.map g)) := by
  induction xs with
  | nil => exact .refl _
  | cons head tail ih =>
      exact (((pointwise head List.mem_cons_self).appArg
          (.app (.const Intrinsic.consName) element)).appFun _).trans
        ((ih (fun x member => pointwise x (List.mem_cons_of_mem _ member))).appArg _)

/-- Composition is an ordinary open lambda, so fusion's pointwise operation
uses native beta rather than an extra map-fusion rewrite rule. -/
def compose (f g : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (rename wk f) (.app (rename wk g) (.var 0)))

theorem compose_beta (level : LevelExpr) (f g x : Tower.Tm n) :
    Reduces level (.app (compose f g) x) (.app f (.app g x)) := by
  simpa only [compose, inst0, subst, subst_rename, subst0_succ,
    subst0_zero, wk, subst_vars] using Reduces.beta level
    (.app (rename wk f) (.app (rename wk g) (.var 0))) x

/-- Both actual programs reach the same constructor observation. This is
directed execution, not simply the symmetric closure of conversion. -/
theorem fusion_common_output (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n)) :
    Reduces level (applyMap b c f (applyMap a b g (encode a xs)))
        (encode c (xs.map (fun x => .app f (.app g x)))) ∧
      Reduces level (applyMap a c (compose f g) (encode a xs))
        (encode c (xs.map (fun x => .app f (.app g x)))) := by
  constructor
  · have inner := (applyMap_encode level a b g xs).appArg
      (.app (.app (.app (liftClosed nativeMapTerm) b) c) f)
    exact inner.trans (by
      simpa only [List.map_map, Function.comp_def, applyMap] using
        applyMap_encode level b c f (xs.map (fun x => .app g x)))
  · exact (applyMap_encode level a c (compose f g) xs).trans
      (encode_pointwise level c _ _ xs (fun x _ => compose_beta level f g x))

/-- The generated observation of finite computation is exact in both
directions: it does not add a target not reachable by the native rules.
This relational GSLT construction is not the separate textual rule parser. -/
theorem finite_observation_iff (level : LevelExpr)
    (predicate : Tower.Tm n → Prop) (source : Tower.Tm n) :
    gsltDiamond (reduction level n).closure predicate source ↔
      ∃ target, Reduces level source target ∧ predicate target := by
  refine (gsltDiamond_spec (reduction level n).closure predicate source).trans ?_
  constructor
  · rintro ⟨target, ⟨reached, path, same⟩, accepted⟩
    change reached = target at same
    subst target
    exact ⟨reached, path, accepted⟩
  · rintro ⟨target, path, accepted⟩
    exact ⟨target, ⟨target, path, rfl⟩, accepted⟩

theorem map_observed (level : LevelExpr) (source target function : Tower.Tm n)
    (xs : List (Tower.Tm n)) :
    gsltDiamond (reduction level n).closure
      (fun output => output = encode target (xs.map (fun x => .app function x)))
      (applyMap source target function (encode source xs)) := by
  exact (finite_observation_iff level _ _).2
    ⟨_, applyMap_encode level source target function xs, rfl⟩

/-- Any chosen observation of the common output can be consumed after either
native program. This claims existential finite execution, not identical
traces, cost, all executions, or effectful fusion. -/
theorem fusion_observed (level : LevelExpr)
    (a b c f g : Tower.Tm n) (xs : List (Tower.Tm n))
    (predicate : Tower.Tm n → Prop)
    (accepted : predicate (encode c (xs.map (fun x => .app f (.app g x))))) :
    gsltDiamond (reduction level n).closure predicate
        (applyMap b c f (applyMap a b g (encode a xs))) ∧
      gsltDiamond (reduction level n).closure predicate
        (applyMap a c (compose f g) (encode a xs)) := by
  obtain ⟨unfused, fused⟩ := fusion_common_output level a b c f g xs
  constructor
  · exact (finite_observation_iff level _ _).2 ⟨_, unfused, accepted⟩
  · exact (finite_observation_iff level _ _).2 ⟨_, fused, accepted⟩

#print axioms applyMap_beta
#print axioms mapped_encode
#print axioms applyMap_encode
#print axioms Reduces.substitute
#print axioms fusion_common_output
#print axioms finite_observation_iff
#print axioms fusion_observed

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.IntrinsicNativeListMapComputation
