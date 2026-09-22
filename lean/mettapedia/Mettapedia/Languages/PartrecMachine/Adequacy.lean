import Mettapedia.Languages.PartrecMachine.LanguageDef
import Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.GSLT.Meredith.GSLT

/-!
# Adequacy of the authored partial-recursive machine

`partrecMachine` is Mathlib's `Turing.ToPartrec` machine authored as a
`LanguageDef`.  This module proves that reduction in the authored language
computes exactly what Mathlib's machine computes.

Mathlib's values, codes, continuations and configurations are encoded injectively
as patterns.  A pending `stepNormal c k v` — which Mathlib evaluates eagerly — is
the configuration `normalTerm c k v`.

* **The generated theory.**  The authored rules are unconditional, so a step is a
  root reduct (`reduces_iff_mem_rootReducts`); the language is equation-free, so
  reduction is the step of the theory the OSLF construction generates from it and
  multi-step reduction is that theory's `MultiStep`
  (`reflTransGen_reduces_iff_multiStep`).
* **One step.**  On an encoded configuration or pending evaluation the engine has
  exactly one reduct (`rootReducts_normal`, `rootReducts_ret`), and a halted
  configuration has none (`halt_irreducible`).  The relation is therefore
  deterministic on that image (`reduces_deterministic`).
* **Forward.**  Each step of Mathlib's machine is a nonempty reduction sequence
  (`step_simulated`), and a pending evaluation reduces to its eager result
  (`normal_reaches_stepNormal`).
* **Backward.**  A reduction ending in a halted configuration is reflected into a
  run of Mathlib's machine (`halting_reflected`).
* **Adequacy.**  `normalTerm c halt v` reduces to the halted configuration with
  output `w` exactly when `w ∈ c.eval v` (`adequacy`); in particular a code that
  diverges on `v` has no halted reduct at all (`divergence_has_no_halted_reduct`).

The reference controls show the statement has content.  A concrete successor
computation reaches its halted configuration.  The variant without the
empty-list clause for `succ` still validates, yet fails adequacy on
`Code.succ` at the empty list, where Mathlib's machine returns `[1]`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.PartrecMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.OSLF.Framework.TypeSynthesis
open Turing.ToPartrec

/-! ## Encodings -/

def encNat : ℕ → Pattern
  | 0 => .apply "Zero" []
  | n + 1 => .apply "Succ" [encNat n]

def encNats : List ℕ → Pattern
  | [] => .apply "Nil" []
  | n :: v => .apply "Cons" [encNat n, encNats v]

def encCode : Code → Pattern
  | .zero' => .apply "ZeroCode" []
  | .succ => .apply "SuccCode" []
  | .tail => .apply "TailCode" []
  | .cons f fs => .apply "ConsCode" [encCode f, encCode fs]
  | .comp f g => .apply "CompCode" [encCode f, encCode g]
  | .case f g => .apply "CaseCode" [encCode f, encCode g]
  | .fix f => .apply "FixCode" [encCode f]

def encCont : Cont → Pattern
  | .halt => .apply "HaltCont" []
  | .cons₁ fs as k => .apply "Cons1Cont" [encCode fs, encNats as, encCont k]
  | .cons₂ ns k => .apply "Cons2Cont" [encNats ns, encCont k]
  | .comp f k => .apply "CompCont" [encCode f, encCont k]
  | .fix f k => .apply "FixCont" [encCode f, encCont k]

def encCfg : Cfg → Pattern
  | .halt v => .apply "Halt" [encNats v]
  | .ret k v => .apply "Ret" [encCont k, encNats v]

/-- A pending `stepNormal c k v`. -/
def normalTerm (c : Code) (k : Cont) (v : List ℕ) : Pattern :=
  .apply "Normal" [encCode c, encCont k, encNats v]

theorem encNat_injective : Function.Injective encNat := by
  intro m n h
  induction m generalizing n with
  | zero => cases n <;> simp_all [encNat]
  | succ m ih =>
      cases n with
      | zero => simp [encNat] at h
      | succ n =>
          simp only [encNat, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
          rw [ih h]

theorem encNats_injective : Function.Injective encNats := by
  intro v w h
  induction v generalizing w with
  | nil => cases w <;> simp_all [encNats]
  | cons n v ih =>
      cases w with
      | nil => simp [encNats] at h
      | cons m w =>
          simp only [encNats, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at h
          rw [encNat_injective h.1, ih h.2]

theorem encCode_injective : Function.Injective encCode := by
  intro c d h
  induction c generalizing d with
  | zero' => cases d <;> simp_all [encCode]
  | succ => cases d <;> simp_all [encCode]
  | tail => cases d <;> simp_all [encCode]
  | cons f fs ihf ihfs =>
      cases d <;> simp only [encCode, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [ihf h.1, ihfs h.2]
  | comp f g ihf ihg =>
      cases d <;> simp only [encCode, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [ihf h.1, ihg h.2]
  | case f g ihf ihg =>
      cases d <;> simp only [encCode, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [ihf h.1, ihg h.2]
  | fix f ih =>
      cases d <;> simp only [encCode, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [ih h]

theorem encCont_injective : Function.Injective encCont := by
  intro k l h
  induction k generalizing l with
  | halt => cases l <;> simp_all [encCont]
  | cons₁ fs as k ih =>
      cases l <;> simp only [encCont, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [encCode_injective h.1, encNats_injective h.2.1, ih h.2.2]
  | cons₂ ns k ih =>
      cases l <;> simp only [encCont, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [encNats_injective h.1, ih h.2]
  | comp f k ih =>
      cases l <;> simp only [encCont, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [encCode_injective h.1, ih h.2]
  | fix f k ih =>
      cases l <;> simp only [encCont, Pattern.apply.injEq, List.cons.injEq, and_true,
        true_and, String.reduceEq, false_and] at h
      rw [encCode_injective h.1, ih h.2]

theorem encCfg_injective : Function.Injective encCfg := by
  intro a b h
  cases a <;> cases b <;> simp only [encCfg, Pattern.apply.injEq, List.cons.injEq, and_true,
    true_and, String.reduceEq, false_and] at h
  · rw [encNats_injective h]
  · rw [encCont_injective h.1, encNats_injective h.2]

theorem normalTerm_ne_encCfg (c : Code) (k : Cont) (v : List ℕ) (cfg : Cfg) :
    normalTerm c k v ≠ encCfg cfg := by
  cases cfg <;> simp [normalTerm, encCfg]

/-! ## Root reducts -/

/-- Every rule is unconditional and places its right side without shifting, since
no rule binds. -/
theorem partrecMachine_unconditional : isUnconditionalAligned partrecMachine = true := by
  decide +kernel

/-- Reduction in the authored language. -/
abbrev Reduces : Pattern → Pattern → Prop := Step base partrecMachine

theorem reduces_iff_mem_rootReducts {term target : Pattern} :
    Reduces term target ↔ target ∈ rootReducts partrecMachine term :=
  step_iff_mem_rootReducts base partrecMachine partrecMachine_unconditional term target

/-! ## The generated theory -/

theorem partrecMachine_equationFree : partrecMachine.isEquationFree = true := by
  have same : partrecMachine.isEquationFree =
      (LanguageDef.ofCore "" ["Nat", "Nats", "Code", "Cont", "Cfg"] terms [] []).isEquationFree := rfl
  rw [same]
  decide +kernel

/-- **Reduction is the step of the theory the OSLF construction generates** from
the authored language. -/
theorem reduces_iff_generatedStep (source target : Pattern) :
    Reduces source target ↔ (langGSLT partrecMachine).Step source target :=
  (langSemanticReduces_iff_langReduces_of_equation_free partrecMachine_equationFree source target).symm

theorem reduces_eq_generatedStep : Reduces = (langGSLT partrecMachine).Step :=
  funext fun source => funext fun target => propext (reduces_iff_generatedStep source target)

theorem reflTransGen_reduces_iff_multiStep (source target : Pattern) :
    Relation.ReflTransGen Reduces source target ↔ (langGSLT partrecMachine).MultiStep source target := by
  refine Iff.trans ?_
    (Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen (langGSLT partrecMachine) source target).symm
  unfold Mettapedia.GSLT.Meredith.GSLTMultiStep
  constructor
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih ((reduces_iff_generatedStep _ _).mp step)
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih ((reduces_iff_generatedStep _ _).mpr step)

/-- What a pending `stepNormal` reduces to in one step. -/
def normalReduct : Code → Cont → List ℕ → Pattern
  | .zero', k, v => encCfg (.ret k (0 :: v))
  | .succ, k, v => encCfg (.ret k [v.headI.succ])
  | .tail, k, v => encCfg (.ret k v.tail)
  | .cons f fs, k, v => normalTerm f (.cons₁ fs v k) v
  | .comp f g, k, v => normalTerm g (.comp f k) v
  | .case f g, k, v =>
      v.headI.rec (normalTerm f k v.tail) fun y _ => normalTerm g k (y :: v.tail)
  | .fix f, k, v => normalTerm f (.fix f k) v

/-- What a returning configuration reduces to in one step. -/
def retReduct : Cont → List ℕ → Pattern
  | .halt, v => encCfg (.halt v)
  | .cons₁ fs as k, v => normalTerm fs (.cons₂ v k) as
  | .cons₂ ns k, v => encCfg (.ret k (ns.headI :: v))
  | .comp f k, v => normalTerm f k v
  | .fix f k, v => if v.headI = 0 then encCfg (.ret k v.tail) else normalTerm f (.fix f k) v.tail

set_option maxHeartbeats 4000000 in
theorem rootReducts_normal (c : Code) (k : Cont) (v : List ℕ) :
    rootReducts partrecMachine (normalTerm c k v) = [normalReduct c k v] := by
  cases c with
  | zero' | cons _ _ | comp _ _ | fix _ =>
      simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, normalReduct, encCode, encCfg, encNats, encNat, encCont,
        matchPattern, matchArgs, mergeBindings, applyBindings]
  | succ | tail =>
      cases v with
      | nil =>
          simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, normalReduct, encCode, encCfg, encNats,
            encNat, matchPattern, matchArgs, mergeBindings, applyBindings]
      | cons n w =>
          simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, normalReduct, encCode, encCfg, encNats,
            encNat, matchPattern, matchArgs, mergeBindings, applyBindings]
  | case f g =>
      rcases v with _ | ⟨_ | y, w⟩ <;>
        simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, normalReduct, encCode, encNats,
          encNat, matchPattern, matchArgs, mergeBindings, applyBindings]

set_option maxHeartbeats 4000000 in
theorem rootReducts_ret (k : Cont) (v : List ℕ) :
    rootReducts partrecMachine (encCfg (.ret k v)) = [retReduct k v] := by
  cases k with
  | halt | cons₁ _ _ _ | comp _ _ =>
      simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, retReduct, encCont, encCfg,
        matchPattern, matchArgs, mergeBindings, applyBindings]
  | cons₂ ns k =>
      cases ns <;>
        simp [rootReducts, partrecMachine_rewrites, rewrites, retReduct, encCont, encCfg, encNats,
          encNat, matchPattern, matchArgs, mergeBindings, applyBindings]
  | fix f k =>
      rcases v with _ | ⟨_ | n, w⟩ <;>
        simp [rootReducts, partrecMachine_rewrites, rewrites, normalTerm, retReduct, encCont, encCfg, encNats,
          encNat, matchPattern, matchArgs, mergeBindings, applyBindings]

set_option maxHeartbeats 4000000 in
theorem rootReducts_halt (v : List ℕ) : rootReducts partrecMachine (encCfg (.halt v)) = [] := by
  simp [rootReducts, partrecMachine_rewrites, rewrites, encCfg, matchPattern]

theorem halt_irreducible (v : List ℕ) (target : Pattern) :
    ¬ Reduces (encCfg (.halt v)) target := by
  rw [reduces_iff_mem_rootReducts, rootReducts_halt]
  simp

theorem reduces_normal_iff {c : Code} {k : Cont} {v : List ℕ} {target : Pattern} :
    Reduces (normalTerm c k v) target ↔ target = normalReduct c k v := by
  rw [reduces_iff_mem_rootReducts, rootReducts_normal, List.mem_singleton]

theorem reduces_ret_iff {k : Cont} {v : List ℕ} {target : Pattern} :
    Reduces (encCfg (.ret k v)) target ↔ target = retReduct k v := by
  rw [reduces_iff_mem_rootReducts, rootReducts_ret, List.mem_singleton]

/-! ## Determinism on the encoded image -/

/-- Encoded configurations and pending evaluations. -/
def InImage (term : Pattern) : Prop :=
  (∃ c k v, term = normalTerm c k v) ∨ ∃ cfg, term = encCfg cfg

theorem reduces_deterministic {term first second : Pattern} (image : InImage term)
    (reducesFirst : Reduces term first) (reducesSecond : Reduces term second) :
    first = second := by
  rcases image with ⟨c, k, v, rfl⟩ | ⟨cfg, rfl⟩
  · rw [reduces_normal_iff.mp reducesFirst, reduces_normal_iff.mp reducesSecond]
  · cases cfg with
    | halt v => exact absurd reducesFirst (halt_irreducible v first)
    | ret k v => rw [reduces_ret_iff.mp reducesFirst, reduces_ret_iff.mp reducesSecond]

theorem normalReduct_inImage (c : Code) (k : Cont) (v : List ℕ) :
    InImage (normalReduct c k v) := by
  cases c with
  | zero' => exact .inr ⟨.ret k (0 :: v), rfl⟩
  | succ => exact .inr ⟨.ret k [v.headI.succ], rfl⟩
  | tail => exact .inr ⟨.ret k v.tail, rfl⟩
  | cons f fs => exact .inl ⟨f, .cons₁ fs v k, v, rfl⟩
  | comp f g => exact .inl ⟨g, .comp f k, v, rfl⟩
  | fix f => exact .inl ⟨f, .fix f k, v, rfl⟩
  | case f g =>
      rcases head : v.headI with _ | y
      · exact .inl ⟨f, k, v.tail, by simp [normalReduct, head]⟩
      · exact .inl ⟨g, k, y :: v.tail, by simp [normalReduct, head]⟩

theorem retReduct_inImage (k : Cont) (v : List ℕ) : InImage (retReduct k v) := by
  cases k with
  | halt => exact .inr ⟨.halt v, rfl⟩
  | cons₂ ns k => exact .inr ⟨.ret k (ns.headI :: v), rfl⟩
  | cons₁ fs as k => exact .inl ⟨fs, .cons₂ v k, as, rfl⟩
  | comp f k => exact .inl ⟨f, k, v, rfl⟩
  | fix f k =>
      by_cases zero : v.headI = 0
      · exact .inr ⟨.ret k v.tail, by simp [retReduct, zero]⟩
      · exact .inl ⟨f, .fix f k, v.tail, by simp [retReduct, zero]⟩

/-- The encoded image is closed under reduction. -/
theorem reduct_inImage {term target : Pattern} (image : InImage term)
    (reduces : Reduces term target) : InImage target := by
  rcases image with ⟨c, k, v, rfl⟩ | ⟨cfg, rfl⟩
  · rw [reduces_normal_iff.mp reduces]
    exact normalReduct_inImage c k v
  · cases cfg with
    | halt v => exact absurd reduces (halt_irreducible v target)
    | ret k v =>
        rw [reduces_ret_iff.mp reduces]
        exact retReduct_inImage k v

/-! ## Forward simulation -/

theorem normal_reaches_stepNormal (c : Code) (k : Cont) (v : List ℕ) :
    Relation.ReflTransGen Reduces (normalTerm c k v) (encCfg (stepNormal c k v)) := by
  induction c generalizing k v with
  | zero' | succ | tail => exact .single (reduces_normal_iff.mpr rfl)
  | cons f fs ihf _ => exact .head (reduces_normal_iff.mpr rfl) (ihf _ _)
  | comp f g _ ihg => exact .head (reduces_normal_iff.mpr rfl) (ihg _ _)
  | fix f ihf => exact .head (reduces_normal_iff.mpr rfl) (ihf _ _)
  | case f g ihf ihg =>
      rcases head : v.headI with _ | y
      · refine .head (b := normalTerm f k v.tail) (reduces_normal_iff.mpr ?_) ?_
        · simp [normalReduct, head]
        · simpa [stepNormal, head] using ihf k v.tail
      · refine .head (b := normalTerm g k (y :: v.tail)) (reduces_normal_iff.mpr ?_) ?_
        · simp [normalReduct, head]
        · simpa [stepNormal, head] using ihg k (y :: v.tail)

theorem ret_reaches_stepRet (k : Cont) (v : List ℕ) :
    Relation.TransGen Reduces (encCfg (.ret k v)) (encCfg (stepRet k v)) := by
  induction k generalizing v with
  | halt => exact .single (reduces_ret_iff.mpr rfl)
  | cons₁ fs as k _ => exact .head' (reduces_ret_iff.mpr rfl) (normal_reaches_stepNormal _ _ _)
  | cons₂ ns k ih => exact .head (reduces_ret_iff.mpr rfl) (ih _)
  | comp f k _ => exact .head' (reduces_ret_iff.mpr rfl) (normal_reaches_stepNormal _ _ _)
  | fix f k ih =>
      by_cases zero : v.headI = 0
      · refine .head (b := encCfg (.ret k v.tail)) (reduces_ret_iff.mpr ?_) ?_
        · simp [retReduct, zero]
        · simpa [stepRet, zero] using ih v.tail
      · refine .head' (b := normalTerm f (.fix f k) v.tail) (reduces_ret_iff.mpr ?_) ?_
        · simp [retReduct, zero]
        · simpa [stepRet, zero] using normal_reaches_stepNormal f (.fix f k) v.tail

/-- **Each step of Mathlib's machine is a nonempty reduction sequence.** -/
theorem step_simulated {cfg next : Cfg} (stepped : next ∈ step cfg) :
    Relation.TransGen Reduces (encCfg cfg) (encCfg next) := by
  cases cfg with
  | halt v => simp [step] at stepped
  | ret k v =>
      simp only [step, Option.mem_def, Option.some.injEq] at stepped
      subst stepped
      exact ret_reaches_stepRet k v

theorem reaches_simulated {cfg target : Cfg} (reaches : StateTransition.Reaches step cfg target) :
    Relation.ReflTransGen Reduces (encCfg cfg) (encCfg target) := by
  induction reaches with
  | refl => exact .refl
  | tail _ stepped ih => exact ih.trans (step_simulated stepped).to_reflTransGen

/-! ## Backward simulation -/

theorem reaches_stepRet_of_reaches_ret {k : Cont} {v w : List ℕ}
    (reaches : StateTransition.Reaches step (.ret k v) (.halt w)) :
    StateTransition.Reaches step (stepRet k v) (.halt w) := by
  rcases Relation.ReflTransGen.cases_head reaches with same | ⟨next, stepped, rest⟩
  · cases same
  · simp only [step, Option.mem_def, Option.some.injEq] at stepped
    subst stepped
    exact rest

/-- **A halting reduction is a halting run.**  Stated for both kinds of term in
the encoded image, since a reduction alternates between them. -/
theorem halting_reflected {term : Pattern} {w : List ℕ}
    (reduces : Relation.ReflTransGen Reduces term (encCfg (.halt w))) :
    (∀ cfg, term = encCfg cfg → StateTransition.Reaches step cfg (.halt w)) ∧
      (∀ c k v, term = normalTerm c k v → StateTransition.Reaches step (stepNormal c k v) (.halt w)) := by
  induction reduces using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨fun cfg same => ?_, fun c k v same => ?_⟩
      · rw [encCfg_injective same.symm]
        exact .refl
      · exact absurd same.symm (normalTerm_ne_encCfg c k v _)
  | head reducesHead _ ih =>
      obtain ⟨ihCfg, ihNormal⟩ := ih
      refine ⟨fun cfg same => ?_, fun c k v same => ?_⟩
      · subst same
        cases cfg with
        | halt v => exact absurd reducesHead (halt_irreducible v _)
        | ret k v =>
            have next := reduces_ret_iff.mp reducesHead
            refine .head (show stepRet k v ∈ step (.ret k v) from rfl) ?_
            cases k with
            | halt => exact ihCfg (.halt v) next
            | cons₁ fs as k => exact ihNormal fs (.cons₂ v k) as next
            | cons₂ ns k =>
                exact (reaches_stepRet_of_reaches_ret (ihCfg (.ret k (ns.headI :: v)) next) :
                  StateTransition.Reaches step (stepRet k (ns.headI :: v)) (.halt w))
            | comp f k => exact ihNormal f k v next
            | fix f k =>
                by_cases zero : v.headI = 0
                · simp only [retReduct, zero, if_true] at next
                  rw [show stepRet (.fix f k) v = stepRet k v.tail by simp [stepRet, zero]]
                  exact reaches_stepRet_of_reaches_ret (ihCfg (.ret k v.tail) next)
                · simp only [retReduct, zero, if_false] at next
                  rw [show stepRet (.fix f k) v = stepNormal f (.fix f k) v.tail by
                    simp [stepRet, zero]]
                  exact ihNormal f (.fix f k) v.tail next
      · subst same
        have next := reduces_normal_iff.mp reducesHead
        cases c with
        | zero' => exact ihCfg (.ret k (0 :: v)) next
        | succ => exact ihCfg (.ret k [v.headI.succ]) next
        | tail => exact ihCfg (.ret k v.tail) next
        | cons f fs => exact ihNormal f (.cons₁ fs v k) v next
        | comp f g => exact ihNormal g (.comp f k) v next
        | fix f => exact ihNormal f (.fix f k) v next
        | case f g =>
            rcases head : v.headI with _ | y
            · simp only [normalReduct, head] at next
              rw [show stepNormal (.case f g) k v = stepNormal f k v.tail by
                simp [stepNormal, head]]
              exact ihNormal f k v.tail next
            · simp only [normalReduct, head] at next
              rw [show stepNormal (.case f g) k v = stepNormal g k (y :: v.tail) by
                simp [stepNormal, head]]
              exact ihNormal g k (y :: v.tail) next

/-! ## Adequacy -/

/-- **Adequacy.**  The authored language halts with output `w` from `c` on `v`
exactly when Mathlib's evaluation of `c` on `v` returns `w`. -/
theorem adequacy (c : Code) (v w : List ℕ) :
    Relation.ReflTransGen Reduces (normalTerm c .halt v) (encCfg (.halt w)) ↔ w ∈ c.eval v := by
  have evaluated := stepNormal_eval c v
  constructor
  · intro reduces
    have reaches := (halting_reflected reduces).2 c .halt v rfl
    have member : Cfg.halt w ∈ StateTransition.eval step (stepNormal c .halt v) :=
      StateTransition.mem_eval.mpr ⟨reaches, rfl⟩
    rw [evaluated] at member
    obtain ⟨output, outputMember, same⟩ := (Part.mem_map_iff _).mp member
    cases same
    exact outputMember
  · intro member
    have mapped : Cfg.halt w ∈ StateTransition.eval step (stepNormal c .halt v) := by
      rw [evaluated]
      exact Part.mem_map _ member
    exact (normal_reaches_stepNormal c .halt v).trans
      (reaches_simulated (StateTransition.mem_eval.mp mapped).1)

/-- A diverging code has no halted reduct. -/
theorem divergence_has_no_halted_reduct {c : Code} {v : List ℕ}
    (diverges : c.eval v = Part.none) (w : List ℕ) :
    ¬ Relation.ReflTransGen Reduces (normalTerm c .halt v) (encCfg (.halt w)) := by
  rw [adequacy, diverges]
  exact Part.notMem_none w

/-! ## Reference controls -/

/-- Successor on `[2]` halts with `[3]`. -/
theorem succ_two_halts_with_three :
    Relation.ReflTransGen Reduces (normalTerm .succ .halt [2]) (encCfg (.halt [3])) :=
  (adequacy .succ [2] [3]).mpr (by simp [Code.eval])

/-- Without the empty-list clause for `succ`, the authored language no longer
computes Mathlib's `Code.succ` at the empty list, although that variant still
validates (`withoutSuccOnEmpty_validate_eq_nil`). -/
theorem withoutSuccOnEmpty_not_adequate :
    [1] ∈ Code.succ.eval [] ∧
      ¬ Relation.ReflTransGen (Step base withoutSuccOnEmpty)
        (normalTerm .succ .halt []) (encCfg (.halt [1])) := by
  refine ⟨by simp [Code.eval], fun reduces => ?_⟩
  rcases Relation.ReflTransGen.cases_head reduces with same | ⟨next, stepped, _⟩
  · exact normalTerm_ne_encCfg _ _ _ _ same
  · exact withoutSuccOnEmpty_stuck next stepped

/-! ## Axiom audit -/

#print axioms reflTransGen_reduces_iff_multiStep
#print axioms encCfg_injective
#print axioms reduces_deterministic
#print axioms reduct_inImage
#print axioms step_simulated
#print axioms halting_reflected
#print axioms adequacy
#print axioms divergence_has_no_halted_reduct
#print axioms succ_two_halts_with_three
#print axioms withoutSuccOnEmpty_not_adequate

end Mettapedia.Languages.PartrecMachine
