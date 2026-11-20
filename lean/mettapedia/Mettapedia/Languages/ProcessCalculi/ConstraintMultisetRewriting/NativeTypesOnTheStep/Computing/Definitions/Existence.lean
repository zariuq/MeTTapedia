import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Whole
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Correspondence

/-!
# Every ground call of the compiled function answers: existence by induction on the numeral

**The check** (`existenceCheck`), by the package's executable reduction on open terms: the compiled
function applied to its variables reduces to an inner recursor `num-rec P Z S n` applied to the later
parameters, with `P`, `Z`, `S` looking only at the earlier parameters (`innerParts`); and the inner
recursor's call at `zero`, and at `succ n`, normalizes to an **answer shape** (`Shape`): variables under
`zero`, `succ`, `tt`, pairs and projections, and calls of the inner recursor at `n` on arguments of
that shape.

**The theorem** (`call_exists`): for every compiled function that passes the check, every call at a
numeral and at normal arguments has an answer. By induction on the numeral: the call reduces to the
shape's instance, whose recursive calls are calls at the predecessor, at normal arguments once their
own arguments are answered (`inner_answers`, `Shape.answer`). A projection of a normal term answers
whether or not the term is a pair, so the arguments need only be normal.

**With the typing of calls** (`call_typed`, `call_answers`), for addition by rows and for append on it:
every ground call at a numeral and normal arguments typed along the telescope has exactly one answer,
of the call's declared type (`add_exactly_one`, `appendR_exactly_one`). The check also passes for the
checker's `append` and for the accumulating `sumAcc` (`append_existence`, `acc_existence`). It does not
pass for `map`, whose `cons` row applies the function argument: an application of a variable is no
answer shape (`map_existence_not_checked`), and its answers would need the normalization of the
argument's body.

These are statements about the compiled term, the interpretation of a definition in the package
without new rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TelescopeAbstraction (applyClosed)
open ConversionCoherence (StepStar)
open AlgebraicParallel (stepStar_map)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open Vectors (numRecAt vecNormalize vecNormalize_sound const_normal succ_normal pair_normal)

/-! ## Reduction under substitution and in spines -/

theorem stepStar_subst {n m : Nat} (σ : Sub Tower.Head n m) {t u : Tower.Tm n}
    (steps : StepStar pkg t u) : StepStar pkg (subst σ t) (subst σ u) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (StepCore.substitute step σ)

theorem stepStar_spine_head {n : Nat} {g g' : Tower.Tm n} (steps : StepStar pkg g g') :
    ∀ (as : List (Tower.Tm n)), StepStar pkg (spine g as) (spine g' as)
  | [] => steps
  | a :: as => stepStar_spine_head (stepStar_map (fun t => Tm.app t a) (fun step => Step.congAppFun step) steps) as

theorem stepStar_spine_args {n : Nat} : ∀ (g : Tower.Tm n) {as bs : List (Tower.Tm n)},
    List.Forall₂ (StepStar pkg) as bs → StepStar pkg (spine g as) (spine g bs)
  | _, [], [], .nil => .refl
  | g, _ :: as, b :: _, .cons hab rest =>
      .trans (stepStar_spine_head (stepStar_map (fun t => Tm.app g t) (fun step => Step.congAppArg step) hab) as)
        (stepStar_spine_args (.app g b) rest)

/-! ## Normal forms -/

theorem pair_fst_normal {n : Nat} {a b : Tower.Tm n} (normal : ConstructorSystem.Normal pkg (.pair a b)) :
    ConstructorSystem.Normal pkg a := fun step => normal (.congPairFst step)

theorem pair_snd_normal {n : Nat} {a b : Tower.Tm n} (normal : ConstructorSystem.Normal pkg (.pair a b)) :
    ConstructorSystem.Normal pkg b := fun step => normal (.congPairSnd step)

theorem fst_normal {n : Nat} {t : Tower.Tm n} (normal : ConstructorSystem.Normal pkg t)
    (notPair : ∀ a b, t ≠ .pair a b) : ConstructorSystem.Normal pkg (.fst t) := by
  intro target step
  cases step with
  | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h rfl
  | betaSigmaFst => exact notPair _ _ rfl
  | congFst inner => exact normal inner

theorem snd_normal {n : Nat} {t : Tower.Tm n} (normal : ConstructorSystem.Normal pkg t)
    (notPair : ∀ a b, t ≠ .pair a b) : ConstructorSystem.Normal pkg (.snd t) := by
  intro target step
  cases step with
  | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h rfl
  | betaSigmaSnd => exact notPair _ _ rfl
  | congSnd inner => exact normal inner

/-- An answer of a projection, from an answer of its argument. -/
theorem fst_answer {n : Nat} {t v : Tower.Tm n} (answer : Answer pkg t v) : ∃ w, Answer pkg (.fst t) w := by
  have steps : StepStar pkg (.fst t) (.fst v) := stepStar_map (fun u => Tm.fst u) (fun step => Step.congFst step) answer.1
  by_cases pairShaped : ∃ a b, v = .pair a b
  · obtain ⟨a, b, rfl⟩ := pairShaped
    exact ⟨a, .tail steps (.betaSigmaFst a b), pair_fst_normal answer.2⟩
  · exact ⟨.fst v, steps, fst_normal answer.2 fun a b same => pairShaped ⟨a, b, same⟩⟩

theorem snd_answer {n : Nat} {t v : Tower.Tm n} (answer : Answer pkg t v) : ∃ w, Answer pkg (.snd t) w := by
  have steps : StepStar pkg (.snd t) (.snd v) := stepStar_map (fun u => Tm.snd u) (fun step => Step.congSnd step) answer.1
  by_cases pairShaped : ∃ a b, v = .pair a b
  · obtain ⟨a, b, rfl⟩ := pairShaped
    exact ⟨b, .tail steps (.betaSigmaSnd a b), pair_snd_normal answer.2⟩
  · exact ⟨.snd v, steps, snd_normal answer.2 fun a b same => pairShaped ⟨a, b, same⟩⟩

/-! ## Method bodies whose instances answer -/

/-- **Answer shapes**: variables under `zero`, `succ`, `tt`, pairs and projections, and calls of the
recursive hypothesis `h` at `q` arguments of the same shape. -/
inductive Shape {n : Nat} (q : Nat) (h : Option (Tower.Tm n)) : Tower.Tm n → Prop
  | var (x : Fin n) : Shape q h (.var x)
  | zero : Shape q h zeroC
  | tt : Shape q h ttC
  | succ {t : Tower.Tm n} : Shape q h t → Shape q h (succC t)
  | pair {a b : Tower.Tm n} : Shape q h a → Shape q h b → Shape q h (.pair a b)
  | fst {t : Tower.Tm n} : Shape q h t → Shape q h (.fst t)
  | snd {t : Tower.Tm n} : Shape q h t → Shape q h (.snd t)
  | call {head : Tower.Tm n} (args : List (Tower.Tm n)) : h = some head → args.length = q →
      (∀ a ∈ args, Shape q h a) → Shape q h (spine head args)

/-- Peel `k` arguments off the right of an application. -/
def unspine {n : Nat} : Nat → Tower.Tm n → Option (Tower.Tm n × List (Tower.Tm n))
  | 0, t => some (t, [])
  | k + 1, .app g a => (unspine k g).map fun p => (p.1, p.2 ++ [a])
  | _ + 1, _ => none

theorem spine_append {n : Nat} : ∀ (g : Tower.Tm n) (as : List (Tower.Tm n)) (a : Tower.Tm n),
    spine g (as ++ [a]) = .app (spine g as) a
  | _, [], _ => rfl
  | g, b :: as, a => spine_append (.app g b) as a

theorem unspine_sound {n : Nat} : ∀ (k : Nat) {t h : Tower.Tm n} {as : List (Tower.Tm n)},
    unspine k t = some (h, as) → t = spine h as ∧ as.length = k
  | 0, t, h, as, found => by
      simp only [unspine, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨rfl, rfl⟩
  | k + 1, .app g a, h, as, found => by
      simp only [unspine] at found
      obtain ⟨p, hp, same⟩ := Option.map_eq_some_iff.mp found
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨rfl, len⟩ := unspine_sound k hp
      exact ⟨(spine_append _ _ _).symm, by simp [len]⟩
  | _ + 1, .var _, _, _, found => by simp [unspine] at found
  | _ + 1, .const _, _, _, found => by simp [unspine] at found
  | _ + 1, .head _, _, _, found => by simp [unspine] at found
  | _ + 1, .pi _ _, _, _, found => by simp [unspine] at found
  | _ + 1, .sigma _ _, _, _, found => by simp [unspine] at found
  | _ + 1, .id _ _ _, _, _, found => by simp [unspine] at found
  | _ + 1, .lam _, _, _, found => by simp [unspine] at found
  | _ + 1, .pair _ _, _, _, found => by simp [unspine] at found
  | _ + 1, .fst _, _, _, found => by simp [unspine] at found
  | _ + 1, .snd _, _, _, found => by simp [unspine] at found
  | _ + 1, .refl _, _, _, found => by simp [unspine] at found

/-- **The decision of answer shapes**, within a budget. -/
def shape? {n : Nat} (q : Nat) (h : Option (Tower.Tm n)) : Nat → Tower.Tm n → Bool
  | 0, _ => false
  | fuel + 1, t =>
      (match h, unspine q t with
        | some head, some (head', args) => head' == head && args.all (fun a => shape? q h fuel a)
        | _, _ => false) ||
      (match t with
        | .var _ => true
        | .const c => c == TowerNumbersModel.zero || c == TowerVectorsModel.tt
        | .app g a =>
            match g with
            | .const c => c == TowerNumbersModel.succ && shape? q h fuel a
            | _ => false
        | .pair a b => shape? q h fuel a && shape? q h fuel b
        | .fst a => shape? q h fuel a
        | .snd a => shape? q h fuel a
        | _ => false)

theorem shape?_sound {n : Nat} {q : Nat} {h : Option (Tower.Tm n)} :
    ∀ (fuel : Nat) {t : Tower.Tm n}, shape? q h fuel t = true → Shape q h t
  | 0, _, found => by simp [shape?] at found
  | fuel + 1, t, found => by
      unfold shape? at found
      rcases Bool.or_eq_true_iff.mp found with call | structural
      · revert call
        cases hh : h with
        | none => simp
        | some head =>
            cases hu : unspine q t with
            | none => simp
            | some p =>
                obtain ⟨head', args⟩ := p
                intro call
                simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at call
                obtain ⟨rfl, all⟩ := call
                obtain ⟨rfl, len⟩ := unspine_sound q hu
                exact .call args rfl len fun a member => shape?_sound fuel (all a member)
      · split at structural
        · exact .var _
        · rename_i c
          simp only [Bool.or_eq_true, beq_iff_eq] at structural
          rcases structural with rfl | rfl
          · exact .zero
          · exact .tt
        · rename_i g a
          split at structural
          · rename_i c
            simp only [Bool.and_eq_true, beq_iff_eq] at structural
            obtain ⟨rfl, inner⟩ := structural
            exact .succ (shape?_sound fuel inner)
          · cases structural
        · simp only [Bool.and_eq_true] at structural
          exact .pair (shape?_sound fuel structural.1) (shape?_sound fuel structural.2)
        · exact .fst (shape?_sound fuel structural)
        · exact .snd (shape?_sound fuel structural)
        · cases structural

theorem answers_of_forall {m : Nat} {σ : Sub Tower.Head m 0} :
    ∀ (args : List (Tower.Tm m)), (∀ a ∈ args, ∃ v, Answer pkg (subst σ a) v) →
      ∃ vs, List.Forall₂ (StepStar pkg) (args.map (subst σ)) vs ∧ vs.length = args.length ∧
        ∀ v ∈ vs, ConstructorSystem.Normal pkg v
  | [], _ => ⟨[], .nil, rfl, fun _ member => absurd member List.not_mem_nil⟩
  | a :: as, all => by
      obtain ⟨v, steps, normal⟩ := all a (List.mem_cons_self ..)
      obtain ⟨vs, forall₂, len, normals⟩ := answers_of_forall as fun a' member => all a' (List.mem_cons_of_mem _ member)
      refine ⟨v :: vs, .cons steps forall₂, by simp [len], fun w member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact normal
      · exact normals w later

/-- **An instance of an answer shape at normal values has an answer**, when the recursive hypothesis
answers at every `q` normal arguments. -/
theorem Shape.answer {m : Nat} {q : Nat} {h : Option (Tower.Tm m)} {t : Tower.Tm m} (shape : Shape q h t)
    {σ : Sub Tower.Head m 0} (values : ∀ x, ConstructorSystem.Normal pkg (σ x))
    (calls : ∀ head, h = some head → ∀ args : List (Tower.Tm 0), args.length = q →
      (∀ a ∈ args, ConstructorSystem.Normal pkg a) → ∃ v, Answer pkg (spine (subst σ head) args) v) :
    ∃ v, Answer pkg (subst σ t) v := by
  induction shape with
  | var x => exact ⟨σ x, .refl, values x⟩
  | zero => exact ⟨zeroC, .refl, const_normal level1 (by decide)⟩
  | tt => exact ⟨ttC, .refl, const_normal level1 (by decide)⟩
  | succ _ ih =>
      obtain ⟨v, steps, normal⟩ := ih
      exact ⟨succC v, stepStar_map (fun u => Tm.app (.const TowerNumbersModel.succ) u)
        (fun step => Step.congAppArg step) steps, succ_normal level1 normal⟩
  | pair _ _ iha ihb =>
      obtain ⟨va, stepsA, normalA⟩ := iha
      obtain ⟨vb, stepsB, normalB⟩ := ihb
      exact ⟨.pair va vb, .trans (stepStar_map (fun u => Tm.pair u _) (fun step => Step.congPairFst step) stepsA)
        (stepStar_map (fun u => Tm.pair va u) (fun step => Step.congPairSnd step) stepsB),
        pair_normal level1 normalA normalB⟩
  | fst _ ih =>
      obtain ⟨v, answer⟩ := ih
      exact fst_answer answer
  | snd _ ih =>
      obtain ⟨v, answer⟩ := ih
      exact snd_answer answer
  | @call head args isHead len _ ihArgs =>
      obtain ⟨vs, forall₂, vsLen, normals⟩ := answers_of_forall args ihArgs
      obtain ⟨w, steps, normal⟩ := calls head isHead vs (by rw [vsLen, len]) normals
      refine ⟨w, ?_, normal⟩
      rw [subst_spine]
      exact .trans (stepStar_spine_args _ forall₂) steps

/-! ## Substitutions that agree where a term looks -/

theorem subst_agree : ∀ {k m : Nat} (p : Fin k → Bool) (t : Tower.Tm k) {σ σ' : Sub Tower.Head k m},
    Vectors.Checker.mentions p t = false → (∀ x, p x = false → σ x = σ' x) → subst σ t = subst σ' t
  | _, _, p, .var i, _, _, missing, agree => agree i missing
  | _, _, _, .const _, _, _, _, _ => rfl
  | _, _, _, .head _, _, _, _, _ => rfl
  | _, _, p, .pi A B, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions, Bool.or_eq_false_iff] at missing
      simp only [subst]
      rw [subst_agree p A missing.1 agree, subst_agree _ B missing.2 (liftSub_agree agree)]
  | _, _, p, .sigma A B, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions, Bool.or_eq_false_iff] at missing
      simp only [subst]
      rw [subst_agree p A missing.1 agree, subst_agree _ B missing.2 (liftSub_agree agree)]
  | _, _, p, .id A a b, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions, Bool.or_eq_false_iff] at missing
      simp only [subst]
      rw [subst_agree p A missing.1.1 agree, subst_agree p a missing.1.2 agree, subst_agree p b missing.2 agree]
  | _, _, p, .lam body, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions] at missing
      simp only [subst]
      rw [subst_agree _ body missing (liftSub_agree agree)]
  | _, _, p, .app g a, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions, Bool.or_eq_false_iff] at missing
      simp only [subst]
      rw [subst_agree p g missing.1 agree, subst_agree p a missing.2 agree]
  | _, _, p, .pair a b, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions, Bool.or_eq_false_iff] at missing
      simp only [subst]
      rw [subst_agree p a missing.1 agree, subst_agree p b missing.2 agree]
  | _, _, p, .fst t, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions] at missing
      simp only [subst]
      rw [subst_agree p t missing agree]
  | _, _, p, .snd t, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions] at missing
      simp only [subst]
      rw [subst_agree p t missing agree]
  | _, _, p, .refl t, σ, σ', missing, agree => by
      simp only [Vectors.Checker.mentions] at missing
      simp only [subst]
      rw [subst_agree p t missing agree]
where
  liftSub_agree {k m : Nat} {p : Fin k → Bool} {σ σ' : Sub Tower.Head k m}
      (agree : ∀ x, p x = false → σ x = σ' x) :
      ∀ x, (Fin.cases (motive := fun _ => Bool) false p x) = false → liftSub σ x = liftSub σ' x := by
    intro x
    refine Fin.cases ?_ (fun y => ?_) x
    · intro _
      rfl
    · intro missing
      simp only [Fin.cases_succ] at missing
      simp only [liftSub, Fin.cases_succ]
      rw [agree y missing]

/-! ## The validation of existence -/

/-- The numeral `succ^N zero`. -/
def nat {n : Nat} : Nat → Tower.Tm n
  | 0 => zeroC
  | k + 1 => succC (nat k)

theorem nat_normal {n : Nat} : ∀ (k : Nat), ConstructorSystem.Normal pkg (nat k : Tower.Tm n)
  | 0 => const_normal level1 (by decide)
  | k + 1 => succ_normal level1 (nat_normal k)

/-- The variables of the context `y₁ … y_q, n, x₀ … x_{j-1}` (newest first), in telescope order. -/
def allVars (q j : Nat) : List (Tower.Tm (q + 1 + j)) := List.ofFn fun i : Fin (q + 1 + j) => .var i.rev

/-- The later parameters, in telescope order. -/
def sufVars (q j : Nat) : List (Tower.Tm (q + 1 + j)) := List.ofFn fun t : Fin q => .var ⟨q - 1 - t, by omega⟩

/-- The call index. -/
def idx (q j : Nat) : Fin (q + 1 + j) := ⟨q, by omega⟩

/-- **The inner recursor of a compiled function**, read off the open normal form of its call:
`num-rec P Z S n` applied to the later parameters. -/
def innerParts (fuel : Nat) (c : Tower.Tm 0) (q j : Nat) :
    Option (Tower.Tm (q + 1 + j) × Tower.Tm (q + 1 + j) × Tower.Tm (q + 1 + j)) :=
  match vecNormalize level1 fuel (spine (liftClosed c) (allVars q j)) with
  | some t =>
      match unspine q t with
      | some (h, args) =>
          if args = sufVars q j then
            match h with
            | .app (.app (.app (.app (.const r) P) Z) S) (.var x) =>
                if r = TowerNumbersModel.numRec ∧ x = idx q j then some (P, Z, S) else none
            | _ => none
          else none
      | none => none
  | none => none

/-- **The existence check**: the inner recursor's parts look only at the prefix; at `zero` and at
`succ n` its call on the later parameters normalizes to an answer shape, the recursive hypothesis being
the inner recursor at `n`. -/
def existenceCheck (fuel : Nat) (c : Tower.Tm 0) (q j : Nat) : Bool :=
  match innerParts fuel c q j with
  | some (P, Z, S) =>
      Vectors.Checker.mentions (fun x => decide (x.val ≤ q)) P == false &&
      Vectors.Checker.mentions (fun x => decide (x.val ≤ q)) Z == false &&
      Vectors.Checker.mentions (fun x => decide (x.val ≤ q)) S == false &&
      (match vecNormalize level1 fuel (spine (numRecAt P Z S zeroC) (sufVars q j)) with
        | some B => shape? q none fuel B
        | none => false) &&
      (match vecNormalize level1 fuel (spine (numRecAt P Z S (succC (.var (idx q j)))) (sufVars q j)) with
        | some B => shape? q (some (numRecAt P Z S (.var (idx q j)))) fuel B
        | none => false)
  | none => false

/-- **Reading the inner recursor back**: the call on the variables reduces to it. -/
theorem innerParts_sound {fuel : Nat} {c : Tower.Tm 0} {q j : Nat} {P Z S : Tower.Tm (q + 1 + j)}
    (found : innerParts fuel c q j = some (P, Z, S)) :
    StepStar pkg (spine (liftClosed c) (allVars q j)) (spine (numRecAt P Z S (.var (idx q j))) (sufVars q j)) := by
  unfold innerParts at found
  split at found
  · rename_i t ht
    split at found
    · rename_i h args hu
      split at found
      · rename_i same
        split at found
        · rename_i r P' Z' S' x
          split at found
          · rename_i cond
            obtain ⟨rfl, rfl⟩ := cond
            simp only [Option.some.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, rfl, rfl⟩ := found
            obtain ⟨rfl, -⟩ := unspine_sound q hu
            subst same
            exact vecNormalize_sound level1 ht
          · cases found
        · cases found
      · cases found
    · cases found
  · cases found

/-- `σ` with the later parameters set to `suf` and the call index to `i`. -/
def override {q j : Nat} (σ : Sub Tower.Head (q + 1 + j) 0) (suf : List (Tower.Tm 0)) (i : Tower.Tm 0) :
    Sub Tower.Head (q + 1 + j) 0 := fun x =>
  if x.val < q then suf.getD (q - 1 - x.val) zeroC else if x.val = q then i else σ x

theorem getD_normal {suf : List (Tower.Tm 0)} (normals : ∀ v ∈ suf, ConstructorSystem.Normal pkg v) (k : Nat) :
    ConstructorSystem.Normal pkg (suf.getD k zeroC) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : suf[k]? with
  | none => exact const_normal level1 (by decide)
  | some v => exact normals v (List.mem_of_getElem? h)

theorem override_normal {q j : Nat} {σ : Sub Tower.Head (q + 1 + j) 0} (values : ∀ x, ConstructorSystem.Normal pkg (σ x))
    {suf : List (Tower.Tm 0)} (normals : ∀ v ∈ suf, ConstructorSystem.Normal pkg v) {i : Tower.Tm 0}
    (normalI : ConstructorSystem.Normal pkg i) : ∀ x, ConstructorSystem.Normal pkg (override σ suf i x) := by
  intro x
  unfold override
  split
  · exact getD_normal normals _
  · split
    · exact normalI
    · exact values x

theorem override_agree {q j : Nat} (σ : Sub Tower.Head (q + 1 + j) 0) (suf : List (Tower.Tm 0)) (i : Tower.Tm 0) :
    ∀ x, decide (x.val ≤ q) = false → σ x = override σ suf i x := by
  intro x far
  have : ¬ x.val ≤ q := of_decide_eq_false far
  unfold override
  rw [if_neg (by omega), if_neg (by omega)]

theorem override_idx {q j : Nat} (σ : Sub Tower.Head (q + 1 + j) 0) (suf : List (Tower.Tm 0)) (i : Tower.Tm 0) :
    override σ suf i (idx q j) = i := by
  unfold override idx
  simp

theorem sufVars_override {q j : Nat} (σ : Sub Tower.Head (q + 1 + j) 0) {suf : List (Tower.Tm 0)} (i : Tower.Tm 0)
    (len : suf.length = q) : (sufVars q j).map (subst (override σ suf i)) = suf := by
  apply List.ext_getElem
  · simp [sufVars, len]
  · intro t h₁ h₂
    simp only [sufVars, List.getElem_map, List.getElem_ofFn, subst, override]
    have lt : t < q := by simpa [sufVars] using h₁
    rw [if_pos (by omega)]
    have same : q - 1 - (q - 1 - t) = t := by omega
    simp only [same, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

theorem sufVars_values {q j : Nat} (σ : Sub Tower.Head (q + 1 + j) 0) (values : ∀ x, ConstructorSystem.Normal pkg (σ x)) :
    ∀ v ∈ (sufVars q j).map (subst σ), ConstructorSystem.Normal pkg v := by
  intro v member
  obtain ⟨t, tm, rfl⟩ := List.mem_map.mp member
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp tm
  exact values _

theorem subst_numRecAt {n m : Nat} (σ : Sub Tower.Head n m) (P Z S t : Tower.Tm n) :
    subst σ (numRecAt P Z S t) = numRecAt (subst σ P) (subst σ Z) (subst σ S) (subst σ t) := rfl

/-- **The inner recursor answers at every numeral**, at normal values of its parameters. -/
theorem inner_answers {fuel : Nat} {c : Tower.Tm 0} {q j : Nat} (check : existenceCheck fuel c q j = true)
    {P Z S : Tower.Tm (q + 1 + j)} (found : innerParts fuel c q j = some (P, Z, S)) :
    ∀ (N : Nat) (σ : Sub Tower.Head (q + 1 + j) 0), (∀ x, ConstructorSystem.Normal pkg (σ x)) →
      ∀ (suf : List (Tower.Tm 0)), suf.length = q → (∀ v ∈ suf, ConstructorSystem.Normal pkg v) →
        ∃ v, Answer pkg (spine (numRecAt (subst σ P) (subst σ Z) (subst σ S) (nat N)) suf) v := by
  unfold existenceCheck at check
  rw [found] at check
  simp only [Bool.and_eq_true, beq_iff_eq] at check
  obtain ⟨⟨⟨⟨noP, noZ⟩, noneOfS⟩, zeroCase⟩, succCase⟩ := check
  split at zeroCase
  · rename_i B₀ h₀
    split at succCase
    · rename_i B₁ h₁
      have shape₀ := shape?_sound fuel zeroCase
      have shape₁ := shape?_sound fuel succCase
      have sameP := fun σ suf i => subst_agree _ P noP (override_agree σ suf i)
      have sameZ := fun σ suf i => subst_agree _ Z noZ (override_agree σ suf i)
      have sameS := fun σ suf i => subst_agree _ S noneOfS (override_agree σ suf i)
      intro N
      induction N with
      | zero =>
          intro σ values suf len normals
          have inst := stepStar_subst (override σ suf zeroC) (vecNormalize_sound level1 h₀)
          rw [subst_spine, subst_numRecAt, sufVars_override σ zeroC len] at inst
          rw [← sameP σ suf zeroC, ← sameZ σ suf zeroC, ← sameS σ suf zeroC] at inst
          obtain ⟨v, answer⟩ := shape₀.answer (override_normal values normals (nat_normal 0))
            (fun _ none _ _ _ => by cases none)
          exact ⟨v, inst.trans answer.1, answer.2⟩
      | succ N ih =>
          intro σ values suf len normals
          have inst := stepStar_subst (override σ suf (nat N)) (vecNormalize_sound level1 h₁)
          rw [subst_spine, subst_numRecAt, sufVars_override σ (nat N) len] at inst
          rw [← sameP σ suf (nat N), ← sameZ σ suf (nat N), ← sameS σ suf (nat N)] at inst
          have index : subst (override σ suf (nat N)) (succC (.var (idx q j))) = nat (N + 1) := by
            show succC (override σ suf (nat N) (idx q j)) = succC (nat N)
            rw [override_idx]
          rw [index] at inst
          obtain ⟨v, answer⟩ := shape₁.answer (override_normal values normals (nat_normal N))
            (fun head same args argsLen argsNormal => by
              obtain rfl := Option.some.inj same
              rw [subst_numRecAt, ← sameP σ suf (nat N), ← sameZ σ suf (nat N), ← sameS σ suf (nat N)]
              show ∃ v, Answer pkg (spine (numRecAt (subst σ P) (subst σ Z) (subst σ S)
                (override σ suf (nat N) (idx q j))) args) v
              rw [override_idx]
              exact ih σ values args argsLen argsNormal)
          exact ⟨v, inst.trans answer.1, answer.2⟩
    · cases succCase
  · cases zeroCase

/-- **Every call of a function that passes the existence check, at a numeral and normal arguments, has
an answer.** -/
theorem call_exists {fuel : Nat} {c : Tower.Tm 0} {q j : Nat} (check : existenceCheck fuel c q j = true)
    (σ : Sub Tower.Head (q + 1 + j) 0) (values : ∀ x, ConstructorSystem.Normal pkg (σ x)) {N : Nat}
    (index : σ (idx q j) = nat N) : ∃ v, Answer pkg (spine c ((allVars q j).map (subst σ))) v := by
  have parts : ∃ P Z S, innerParts fuel c q j = some (P, Z, S) := by
    unfold existenceCheck at check
    split at check
    · rename_i P Z S found
      exact ⟨P, Z, S, found⟩
    · cases check
  obtain ⟨P, Z, S, found⟩ := parts
  have inst := stepStar_subst σ (innerParts_sound found)
  rw [subst_spine, subst_spine, subst_liftClosed, TelescopeAbstraction.liftClosed_zero, subst_numRecAt] at inst
  have atIndex : subst σ (.var (idx q j) : Tower.Tm (q + 1 + j)) = nat N := index
  rw [atIndex] at inst
  obtain ⟨v, answer⟩ := inner_answers check found N σ values ((sufVars q j).map (subst σ))
    (by simp [sufVars]) (sufVars_values σ values)
  exact ⟨v, inst.trans answer.1, answer.2⟩

/-! ## The instances -/

theorem add_existence : existenceCheck 30 addTerm 1 0 = true := by decide +kernel

theorem appendR_existence : existenceCheck 40 appendRTerm 3 1 = true := by decide +kernel

theorem append_existence :
    ((compile 0 Vectors.Checker.appendDef).map fun c => existenceCheck 40 c 3 1) = some true := by
  decide +kernel

theorem acc_existence : ((compile 0 accDef).map fun c => existenceCheck 30 c 1 0) = some true := by
  decide +kernel

/-- **The check does not pass for `map`**: its `cons` row applies the function argument. -/
theorem map_existence_not_checked :
    ((compile 0 mapDef).map fun c => existenceCheck 40 c 1 3) = some false := by
  decide +kernel

theorem nat_typed : ∀ (N : Nat), Typed pkg .nil (nat N) numC
  | 0 => D.zero_typed
  | N + 1 => D.succ_typed (nat_typed N)

/-- **Every ground call of addition by rows, at a numeral and a normal number, has exactly one answer,
a number.** -/
theorem add_exactly_one (N : Nat) {m : Tower.Tm 0} (typed : Typed pkg .nil m numC)
    (normal : ConstructorSystem.Normal pkg m) :
    ∃ v, Answer pkg (spine addTerm [nat N, m]) v ∧ Typed pkg .nil v numC ∧
      ∀ v', Answer pkg (spine addTerm [nat N, m]) v' → v' = v := by
  let σ : Sub Tower.Head 2 0 := fun x => if x.val = 0 then m else nat N
  have values : ∀ x, ConstructorSystem.Normal pkg (σ x) := by
    intro x
    show ConstructorSystem.Normal pkg (if x.val = 0 then m else nat N)
    split
    · exact normal
    · exact nat_normal N
  obtain ⟨v, answer⟩ := call_exists add_existence σ values (N := N) rfl
  have call : spine addTerm ((allVars 1 0).map (subst σ)) = applyClosed addDef.telescope σ addTerm := rfl
  rw [call] at answer
  obtain ⟨c, checked⟩ := qualify_closed add_verdict
  obtain rfl : c = addTerm := Option.some.inj (checked.compiled.symm.trans add_compiles)
  have args : SubstMor pkg addDef.telescope (baseCtx addDef 0) σ := by
    intro x
    match x with
    | ⟨0, _⟩ => exact typed
    | ⟨1, _⟩ => exact nat_typed N
  obtain ⟨vTyped, -, unique⟩ := call_answers .nil (call_typed checked args) answer
  exact ⟨v, answer, vTyped, unique⟩

/-- **Every ground call of append on the addition by rows**, at arguments typed along its telescope,
normal, with a numeral length, **has exactly one answer, at the call's declared type**. -/
theorem appendR_exactly_one {σ : Sub Tower.Head 5 0} (args : SubstMor pkg appendRDef.telescope .nil σ)
    (values : ∀ x, ConstructorSystem.Normal pkg (σ x)) {N : Nat} (index : σ 3 = nat N) :
    ∃ v, Answer pkg (applyClosed appendRDef.telescope σ appendRTerm) v ∧
      Typed pkg .nil v (subst σ appendRDef.result) ∧
      ∀ v', Answer pkg (applyClosed appendRDef.telescope σ appendRTerm) v' → v' = v := by
  obtain ⟨v, answer⟩ := call_exists appendR_existence σ values (N := N) index
  have call : spine appendRTerm ((allVars 3 1).map (subst σ)) = applyClosed appendRDef.telescope σ appendRTerm := rfl
  rw [call] at answer
  obtain ⟨vTyped, -, unique⟩ := call_answers .nil (call_typed appendR_checked args) answer
  exact ⟨v, answer, vTyped, unique⟩

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.stepStar_subst
#print axioms NativeTypesOnTheStep.Computing.Definitions.Shape.answer
#print axioms NativeTypesOnTheStep.Computing.Definitions.shape?_sound
#print axioms NativeTypesOnTheStep.Computing.Definitions.subst_agree
#print axioms NativeTypesOnTheStep.Computing.Definitions.innerParts_sound
#print axioms NativeTypesOnTheStep.Computing.Definitions.inner_answers
#print axioms NativeTypesOnTheStep.Computing.Definitions.call_exists
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_existence
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_existence
#print axioms NativeTypesOnTheStep.Computing.Definitions.append_existence
#print axioms NativeTypesOnTheStep.Computing.Definitions.acc_existence
#print axioms NativeTypesOnTheStep.Computing.Definitions.map_existence_not_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_exactly_one
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_exactly_one

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
