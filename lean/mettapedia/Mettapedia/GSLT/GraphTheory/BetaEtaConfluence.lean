import Mettapedia.GSLT.GraphTheory.ParallelReduction

/-!
# βη-reduction is Church–Rosser

One-step β- and η-reduction on de Bruijn λ-terms, where the η-redex is
`λ. (↑f) 0` and contracts to `f`.  The proof follows Hindley and Rosen:

* shifting is injective and can be inverted through β- and η-steps
  (`betaStep_shift_inv`, `etaStep_shift_inv`), and both kinds of step are
  stable under shifting (`betaStep_shift`, `etaStep_shift`);
* η-steps are stable under substitution, and an η-step in a substituted term
  gives η-steps in the result (`etaStep_subst`, `etaStar_subst_arg`);
* η-reduction has the diamond property up to reflexivity, hence is confluent
  (`etaStar_confluent`); β-reduction is confluent through parallel reduction
  (`betaStar_confluent`);
* a β-step and an η-step from one term close with η-steps on one side and at
  most one β-step on the other (`beta_eta_diagram`), so the reflexive-transitive
  closures commute (`betaStar_etaStar_commute`);
* hence βη-reduction is confluent (`betaEtaStar_confluent`) and βη-conversion
  is joinability (`join_of_betaEtaConv`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GraphTheory.BetaEta

open Mettapedia.GSLT.GraphTheory
open LambdaTerm

/-! ## Shifting: injectivity and inversion -/

theorem shift_var_exists (d c n : ℕ) : ∃ m, shift d c (.var n) = .var m := by
  by_cases below : n < c
  · exact ⟨n, shift_var_lt n d c below⟩
  · exact ⟨n + d, shift_var_ge n d c (by omega)⟩

theorem shift_injective (d c : ℕ) {first second : LambdaTerm}
    (equal : shift d c first = shift d c second) : first = second := by
  induction first generalizing second c with
  | var m =>
      cases second with
      | var n =>
          by_cases mBelow : m < c <;> by_cases nBelow : n < c
          · rw [shift_var_lt m d c mBelow, shift_var_lt n d c nBelow] at equal
            exact equal
          · rw [shift_var_lt m d c mBelow, shift_var_ge n d c (by omega)] at equal
            injection equal with equal
            omega
          · rw [shift_var_ge m d c (by omega), shift_var_lt n d c nBelow] at equal
            injection equal with equal
            omega
          · rw [shift_var_ge m d c (by omega), shift_var_ge n d c (by omega)] at equal
            injection equal with equal
            exact congrArg LambdaTerm.var (by omega)
      | lam _ =>
          obtain ⟨_, shifted⟩ := shift_var_exists d c m
          rw [shifted] at equal
          cases equal
      | app _ _ =>
          obtain ⟨_, shifted⟩ := shift_var_exists d c m
          rw [shifted] at equal
          cases equal
  | lam body ih =>
      cases second with
      | var n =>
          obtain ⟨_, shifted⟩ := shift_var_exists d c n
          rw [shifted] at equal
          cases equal
      | lam body' =>
          simp only [shift] at equal
          injection equal with equal
          rw [ih (c + 1) equal]
      | app _ _ => cases equal
  | app function argument ihFunction ihArgument =>
      cases second with
      | var n =>
          obtain ⟨_, shifted⟩ := shift_var_exists d c n
          rw [shifted] at equal
          cases equal
      | lam _ => cases equal
      | app function' argument' =>
          simp only [shift] at equal
          injection equal with functionEq argumentEq
          rw [ihFunction c functionEq, ihArgument c argumentEq]

theorem shift_eq_lam {d c : ℕ} {term body : LambdaTerm} (equal : shift d c term = .lam body) :
    ∃ inner, term = .lam inner ∧ body = shift d (c + 1) inner := by
  cases term with
  | var n =>
      obtain ⟨_, shifted⟩ := shift_var_exists d c n
      rw [shifted] at equal
      cases equal
  | lam inner =>
      simp only [shift] at equal
      injection equal with equal
      exact ⟨inner, rfl, equal.symm⟩
  | app _ _ => cases equal

theorem shift_eq_app {d c : ℕ} {term function argument : LambdaTerm}
    (equal : shift d c term = .app function argument) :
    ∃ function' argument', term = .app function' argument' ∧
      function = shift d c function' ∧ argument = shift d c argument' := by
  cases term with
  | var n =>
      obtain ⟨_, shifted⟩ := shift_var_exists d c n
      rw [shifted] at equal
      cases equal
  | lam _ => cases equal
  | app function' argument' =>
      simp only [shift] at equal
      injection equal with functionEq argumentEq
      exact ⟨function', argument', rfl, functionEq.symm, argumentEq.symm⟩

theorem shift_eq_var_zero {d c : ℕ} {term : LambdaTerm} (equal : shift d (c + 1) term = .var 0) :
    term = .var 0 := by
  cases term with
  | var n =>
      by_cases below : n < c + 1
      · rw [shift_var_lt n d (c + 1) below] at equal
        exact equal
      · rw [shift_var_ge n d (c + 1) (by omega)] at equal
        injection equal with equal
        omega
  | lam _ => cases equal
  | app _ _ => cases equal

/-- **Inverting a commuted shift.**  If shifting at a higher cutoff gives a term
shifted at cutoff `k`, the original is itself shifted at `k`. -/
theorem shift_comm_inv (d c : ℕ) : ∀ (k : ℕ) {term shifted : LambdaTerm},
    shift d (c + k + 1) term = shift 1 k shifted →
      ∃ original, term = shift 1 k original ∧ shifted = shift d (c + k) original := by
  intro k term
  induction term generalizing k with
  | var m =>
      intro shifted equal
      cases shifted with
      | var j =>
          by_cases mBelow : m < c + k + 1
          · rw [shift_var_lt m d (c + k + 1) mBelow] at equal
            by_cases jBelow : j < k
            · rw [shift_var_lt j 1 k jBelow] at equal
              injection equal with equal
              subst equal
              exact ⟨.var m, (shift_var_lt m 1 k jBelow).symm,
                (shift_var_lt m d (c + k) (by omega)).symm⟩
            · rw [shift_var_ge j 1 k (by omega)] at equal
              injection equal with equal
              subst equal
              exact ⟨.var j, (shift_var_ge j 1 k (by omega)).symm,
                (shift_var_lt j d (c + k) (by omega)).symm⟩
          · rw [shift_var_ge m d (c + k + 1) (by omega)] at equal
            by_cases jBelow : j < k
            · rw [shift_var_lt j 1 k jBelow] at equal
              injection equal with equal
              exact absurd equal (by omega)
            · rw [shift_var_ge j 1 k (by omega)] at equal
              injection equal with equal
              refine ⟨.var (m - 1), ?_, ?_⟩
              · rw [shift_var_ge (m - 1) 1 k (by omega)]
                congr 1
                omega
              · rw [shift_var_ge (m - 1) d (c + k) (by omega)]
                congr 1
                omega
      | lam _ =>
          obtain ⟨_, shiftedVar⟩ := shift_var_exists d (c + k + 1) m
          rw [shiftedVar] at equal
          cases equal
      | app _ _ =>
          obtain ⟨_, shiftedVar⟩ := shift_var_exists d (c + k + 1) m
          rw [shiftedVar] at equal
          cases equal
  | lam body ih =>
      intro shifted equal
      obtain ⟨inner, rfl, innerEq⟩ := shift_eq_lam equal.symm
      obtain ⟨original, rfl, rfl⟩ := ih (k + 1) innerEq
      exact ⟨.lam original, rfl, rfl⟩
  | app function argument ihFunction ihArgument =>
      intro shifted equal
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app equal.symm
      simp only [shift] at equal
      injection equal with functionEq' argumentEq'
      obtain ⟨functionOriginal, rfl, rfl⟩ := ihFunction k functionEq'
      obtain ⟨argumentOriginal, rfl, rfl⟩ := ihArgument k argumentEq'
      exact ⟨.app functionOriginal argumentOriginal, rfl, rfl⟩

/-- Substituting a variable for itself one level down undoes a shift above it. -/
theorem subst_var_shift_cancel : ∀ (term : LambdaTerm) (cutoff : ℕ),
    subst cutoff (.var cutoff) (shift 1 (cutoff + 1) term) = term
  | .var m, cutoff => by
      by_cases below : m < cutoff + 1
      · rw [shift_var_lt m 1 (cutoff + 1) below]
        rcases Nat.lt_or_ge m cutoff with lt | ge
        · exact subst_var_lt m cutoff lt _
        · have same : m = cutoff := by omega
          subst same
          exact subst_var_eq m _
      · rw [shift_var_ge m 1 (cutoff + 1) (by omega), subst_var_gt (m + 1) cutoff (by omega),
          Nat.add_sub_cancel]
  | .lam body, cutoff => by
      rw [shift_lam, subst_lam, shift_var_ge cutoff 1 0 (Nat.zero_le _),
        subst_var_shift_cancel body (cutoff + 1)]
  | .app function argument, cutoff => by
      rw [shift_app, subst_app, subst_var_shift_cancel function cutoff,
        subst_var_shift_cancel argument cutoff]

/-! ## One-step reductions -/

/-- One β-step, anywhere in a term. -/
inductive BetaStep : LambdaTerm → LambdaTerm → Prop where
  | beta (body argument : LambdaTerm) :
      BetaStep (.app (.lam body) argument) (subst 0 argument body)
  | lam {body body' : LambdaTerm} : BetaStep body body' → BetaStep (.lam body) (.lam body')
  | appL {function function' : LambdaTerm} (argument : LambdaTerm) :
      BetaStep function function' → BetaStep (.app function argument) (.app function' argument)
  | appR (function : LambdaTerm) {argument argument' : LambdaTerm} :
      BetaStep argument argument' → BetaStep (.app function argument) (.app function argument')

/-- One η-step, anywhere in a term: `λ. (↑f) 0` contracts to `f`. -/
inductive EtaStep : LambdaTerm → LambdaTerm → Prop where
  | eta (function : LambdaTerm) : EtaStep (.lam (.app (shift 1 0 function) (.var 0))) function
  | lam {body body' : LambdaTerm} : EtaStep body body' → EtaStep (.lam body) (.lam body')
  | appL {function function' : LambdaTerm} (argument : LambdaTerm) :
      EtaStep function function' → EtaStep (.app function argument) (.app function' argument)
  | appR (function : LambdaTerm) {argument argument' : LambdaTerm} :
      EtaStep argument argument' → EtaStep (.app function argument) (.app function argument')

/-- Many β-steps. -/
abbrev BetaStar := Relation.ReflTransGen BetaStep

/-- Many η-steps. -/
abbrev EtaStar := Relation.ReflTransGen EtaStep

theorem etaStar_lam {body body' : LambdaTerm} (reduces : EtaStar body body') :
    EtaStar (.lam body) (.lam body') := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.lam step)

theorem etaStar_appL {function function' : LambdaTerm} (argument : LambdaTerm)
    (reduces : EtaStar function function') :
    EtaStar (.app function argument) (.app function' argument) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appL argument step)

theorem etaStar_appR (function : LambdaTerm) {argument argument' : LambdaTerm}
    (reduces : EtaStar argument argument') :
    EtaStar (.app function argument) (.app function argument') := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appR function step)

theorem betaStar_lam {body body' : LambdaTerm} (reduces : BetaStar body body') :
    BetaStar (.lam body) (.lam body') := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.lam step)

theorem betaStar_appL {function function' : LambdaTerm} (argument : LambdaTerm)
    (reduces : BetaStar function function') :
    BetaStar (.app function argument) (.app function' argument) := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appL argument step)

theorem betaStar_appR (function : LambdaTerm) {argument argument' : LambdaTerm}
    (reduces : BetaStar argument argument') :
    BetaStar (.app function argument) (.app function argument') := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appR function step)

/-- Map a reflexive step along a step-preserving map. -/
theorem reflGen_map {relation relation' : LambdaTerm → LambdaTerm → Prop}
    (map : LambdaTerm → LambdaTerm)
    (preserves : ∀ source target, relation source target → relation' (map source) (map target))
    {source target : LambdaTerm} (step : Relation.ReflGen relation source target) :
    Relation.ReflGen relation' (map source) (map target) := by
  cases step with
  | refl => exact .refl
  | single step => exact .single (preserves _ _ step)

/-! ## Inverting steps through a shift -/

/-- A β-step out of a shifted term is the shift of a β-step. -/
theorem betaStep_shift_inv {d c : ℕ} {term result : LambdaTerm}
    (step : BetaStep (shift d c term) result) :
    ∃ result', result = shift d c result' ∧ BetaStep term result' := by
  generalize source : shift d c term = shifted at step
  induction step generalizing term c with
  | beta body argument =>
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app source
      obtain ⟨inner, rfl, innerEq⟩ := shift_eq_lam functionEq.symm
      refine ⟨subst 0 argument' inner, ?_, .beta inner argument'⟩
      rw [subst_0_shift, ← innerEq, ← argumentEq]
  | lam _ ih =>
      obtain ⟨inner, rfl, innerEq⟩ := shift_eq_lam source
      obtain ⟨inner', rfl, innerStep⟩ := ih innerEq.symm
      exact ⟨.lam inner', rfl, .lam innerStep⟩
  | appL argument _ ih =>
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app source
      obtain ⟨function'', rfl, functionStep⟩ := ih functionEq.symm
      exact ⟨.app function'' argument', by rw [argumentEq]; rfl, .appL _ functionStep⟩
  | appR function _ ih =>
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app source
      obtain ⟨argument'', rfl, argumentStep⟩ := ih argumentEq.symm
      exact ⟨.app function' argument'', by rw [functionEq]; rfl, .appR _ argumentStep⟩

/-- An η-step out of a shifted term is the shift of an η-step. -/
theorem etaStep_shift_inv {d c : ℕ} {term result : LambdaTerm}
    (step : EtaStep (shift d c term) result) :
    ∃ result', result = shift d c result' ∧ EtaStep term result' := by
  generalize source : shift d c term = shifted at step
  induction step generalizing term c with
  | eta function =>
      obtain ⟨inner, rfl, innerEq⟩ := shift_eq_lam source
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app innerEq.symm
      have argumentZero : argument' = .var 0 := shift_eq_var_zero argumentEq.symm
      subst argumentZero
      obtain ⟨original, rfl, originalEq⟩ :=
        shift_comm_inv d c 0 (functionEq.symm : shift d (c + 0 + 1) function' = shift 1 0 function)
      exact ⟨original, originalEq, .eta original⟩
  | lam _ ih =>
      obtain ⟨inner, rfl, innerEq⟩ := shift_eq_lam source
      obtain ⟨inner', rfl, innerStep⟩ := ih innerEq.symm
      exact ⟨.lam inner', rfl, .lam innerStep⟩
  | appL argument _ ih =>
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app source
      obtain ⟨function'', rfl, functionStep⟩ := ih functionEq.symm
      exact ⟨.app function'' argument', by rw [argumentEq]; rfl, .appL _ functionStep⟩
  | appR function _ ih =>
      obtain ⟨function', argument', rfl, functionEq, argumentEq⟩ := shift_eq_app source
      obtain ⟨argument'', rfl, argumentStep⟩ := ih argumentEq.symm
      exact ⟨.app function' argument'', by rw [functionEq]; rfl, .appR _ argumentStep⟩

/-- β-steps are stable under shifting. -/
theorem betaStep_shift {term term' : LambdaTerm} (step : BetaStep term term') (d c : ℕ) :
    BetaStep (shift d c term) (shift d c term') := by
  induction step generalizing c with
  | beta body argument =>
      show BetaStep (.app (.lam (shift d (c + 1) body)) (shift d c argument))
        (shift d c (subst 0 argument body))
      rw [subst_0_shift]
      exact .beta _ _
  | lam _ ih => exact .lam (ih (c + 1))
  | appL argument _ ih => exact .appL _ (ih c)
  | appR function _ ih => exact .appR _ (ih c)

/-! ## η-steps under shifting and substitution -/

theorem etaStep_shift {term term' : LambdaTerm} (step : EtaStep term term') (d c : ℕ) :
    EtaStep (shift d c term) (shift d c term') := by
  induction step generalizing c with
  | eta function =>
      show EtaStep (.lam (.app (shift d (c + 1) (shift 1 0 function)) (shift d (c + 1) (.var 0))))
        (shift d c function)
      rw [shift_var_lt 0 d (c + 1) (by omega), shift_comm function d c]
      exact .eta _
  | lam _ ih => exact .lam (ih (c + 1))
  | appL argument _ ih => exact .appL _ (ih c)
  | appR function _ ih => exact .appR _ (ih c)

theorem etaStep_subst {term term' : LambdaTerm} (step : EtaStep term term') (index : ℕ)
    (value : LambdaTerm) : EtaStep (subst index value term) (subst index value term') := by
  induction step generalizing index value with
  | eta function =>
      show EtaStep (.lam (.app (subst (index + 1) (shift 1 0 value) (shift 1 0 function))
        (subst (index + 1) (shift 1 0 value) (.var 0)))) (subst index value function)
      rw [subst_var_lt 0 (index + 1) (by omega), subst_shift_comm 1 index value function]
      exact .eta _
  | lam _ ih => exact .lam (ih (index + 1) (shift 1 0 value))
  | appL argument _ ih => exact .appL _ (ih index value)
  | appR function _ ih => exact .appR _ (ih index value)

/-- An η-step in the substituted value gives η-steps in the result. -/
theorem etaStar_subst_arg : ∀ (term : LambdaTerm) (index : ℕ) {value value' : LambdaTerm},
    EtaStep value value' → EtaStar (subst index value term) (subst index value' term)
  | .var n, index, value, value', step => by
      rcases Nat.lt_trichotomy n index with lt | eq | gt
      · rw [subst_var_lt n index lt, subst_var_lt n index lt]
      · subst eq
        rw [subst_var_eq, subst_var_eq]
        exact .single step
      · rw [subst_var_gt n index gt, subst_var_gt n index gt]
  | .lam body, index, value, value', step => by
      rw [subst_lam, subst_lam]
      exact etaStar_lam (etaStar_subst_arg body (index + 1) (etaStep_shift step 1 0))
  | .app function argument, index, value, value', step => by
      rw [subst_app, subst_app]
      exact (etaStar_appL _ (etaStar_subst_arg function index step)).trans
        (etaStar_appR _ (etaStar_subst_arg argument index step))

/-! ## η is confluent -/

/-- The steps out of an η-redex: its contractum, or an η-redex whose function
has stepped. -/
theorem etaStep_of_redex {function result : LambdaTerm}
    (step : EtaStep (.lam (.app (shift 1 0 function) (.var 0))) result) :
    result = function ∨ ∃ function', result = .lam (.app (shift 1 0 function') (.var 0)) ∧
      EtaStep function function' := by
  generalize shiftedEq : shift 1 0 function = shifted at step
  cases step with
  | eta function'' =>
      exact Or.inl (shift_injective 1 0 shiftedEq).symm
  | lam inner =>
      cases inner with
      | appL _ functionStep =>
          subst shiftedEq
          obtain ⟨function', rfl, step'⟩ := etaStep_shift_inv functionStep
          exact Or.inr ⟨function', rfl, step'⟩
      | appR _ zeroStep => cases zeroStep

/-- **The η-diamond**, up to reflexivity. -/
theorem eta_diamond {source left right : LambdaTerm} (leftStep : EtaStep source left)
    (rightStep : EtaStep source right) :
    ∃ meet, Relation.ReflGen EtaStep left meet ∧ Relation.ReflGen EtaStep right meet := by
  induction leftStep generalizing right with
  | eta function =>
      rcases etaStep_of_redex rightStep with rfl | ⟨function', rfl, functionStep⟩
      · exact ⟨right, .refl, .refl⟩
      · exact ⟨function', .single functionStep, .single (.eta function')⟩
  | @lam body body' bodyStep ih =>
      cases rightStep with
      | eta _ =>
          rcases etaStep_of_redex (EtaStep.lam bodyStep) with equal | ⟨function', equal, functionStep⟩
          · exact ⟨right, by rw [equal], .refl⟩
          · exact ⟨function', by rw [equal]; exact .single (.eta function'), .single functionStep⟩
      | lam bodyStep' =>
          obtain ⟨meet, leftMeet, rightMeet⟩ := ih bodyStep'
          exact ⟨.lam meet, reflGen_map _ (fun _ _ step => EtaStep.lam step) leftMeet,
            reflGen_map _ (fun _ _ step => EtaStep.lam step) rightMeet⟩
  | @appL function function' argument functionStep ih =>
      cases rightStep with
      | appL _ functionStep' =>
          obtain ⟨meet, leftMeet, rightMeet⟩ := ih functionStep'
          exact ⟨.app meet argument,
            reflGen_map (fun term => .app term argument)
              (fun _ _ step => EtaStep.appL argument step) leftMeet,
            reflGen_map (fun term => .app term argument)
              (fun _ _ step => EtaStep.appL argument step) rightMeet⟩
      | appR _ argumentStep =>
          exact ⟨.app function' _, .single (.appR _ argumentStep), .single (.appL _ functionStep)⟩
  | @appR function argument argument' argumentStep ih =>
      cases rightStep with
      | appL _ functionStep =>
          exact ⟨.app _ argument', .single (.appL _ functionStep), .single (.appR _ argumentStep)⟩
      | appR _ argumentStep' =>
          obtain ⟨meet, leftMeet, rightMeet⟩ := ih argumentStep'
          exact ⟨.app function meet,
            reflGen_map (fun term => .app function term)
              (fun _ _ step => EtaStep.appR function step) leftMeet,
            reflGen_map (fun term => .app function term)
              (fun _ _ step => EtaStep.appR function step) rightMeet⟩

/-- **η-reduction is confluent.** -/
theorem etaStar_confluent {source left right : LambdaTerm} (toLeft : EtaStar source left)
    (toRight : EtaStar source right) : Relation.Join EtaStar left right :=
  Relation.church_rosser
    (fun _ _ _ leftStep rightStep =>
      let ⟨meet, leftMeet, rightMeet⟩ := eta_diamond leftStep rightStep
      ⟨meet, leftMeet, rightMeet.to_reflTransGen⟩)
    toLeft toRight

/-! ## β is confluent -/

theorem parRed_of_betaStep {source target : LambdaTerm} (step : BetaStep source target) :
    source ⇛ target := by
  induction step with
  | beta body argument => exact beta_to_parRed body argument
  | lam _ ih => exact .lam ih
  | appL argument _ ih => exact .app ih (ParRed.refl argument)
  | appR function _ ih => exact .app (ParRed.refl function) ih

theorem betaStar_of_parRed {source target : LambdaTerm} (step : source ⇛ target) :
    BetaStar source target := by
  induction step with
  | var n => exact .refl
  | lam _ ih => exact betaStar_lam ih
  | app _ _ functionIh argumentIh =>
      exact (betaStar_appL _ functionIh).trans (betaStar_appR _ argumentIh)
  | @beta body body' argument argument' _ _ bodyIh argumentIh =>
      exact ((betaStar_appL _ (betaStar_lam bodyIh)).trans (betaStar_appR _ argumentIh)).tail
        (.beta body' argument')

theorem betaStar_iff_parRedStar {source target : LambdaTerm} :
    BetaStar source target ↔ (source ⇛* target) := by
  constructor
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail (parRed_of_betaStep step)
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih => exact ih.trans (betaStar_of_parRed step)

/-- **β-reduction is confluent.** -/
theorem betaStar_confluent {source left right : LambdaTerm} (toLeft : BetaStar source left)
    (toRight : BetaStar source right) : Relation.Join BetaStar left right := by
  obtain ⟨meet, leftMeet, rightMeet⟩ :=
    confluence (betaStar_iff_parRedStar.mp toLeft) (betaStar_iff_parRedStar.mp toRight)
  exact ⟨meet, betaStar_iff_parRedStar.mpr leftMeet, betaStar_iff_parRedStar.mpr rightMeet⟩

/-! ## β and η commute -/

/-- **The β/η diagram.**  A β-step and an η-step from one term close with
η-steps after the β-step and at most one β-step after the η-step. -/
theorem beta_eta_diagram {source afterBeta afterEta : LambdaTerm}
    (betaStep : BetaStep source afterBeta) (etaStep : EtaStep source afterEta) :
    ∃ meet, EtaStar afterBeta meet ∧ Relation.ReflGen BetaStep afterEta meet := by
  induction betaStep generalizing afterEta with
  | beta body argument =>
      cases etaStep with
      | appL _ functionStep =>
          cases functionStep with
          | eta _ =>
              refine ⟨_, ?_, .refl⟩
              rw [subst_app, subst_shift_cancel, subst_var_eq]
          | lam bodyStep =>
              exact ⟨_, .single (etaStep_subst bodyStep 0 argument), .single (.beta _ argument)⟩
      | appR _ argumentStep =>
          exact ⟨_, etaStar_subst_arg body 0 argumentStep, .single (.beta body _)⟩
  | @lam body body' bodyStep ih =>
      cases etaStep with
      | eta _ =>
          generalize shiftedEq : shift 1 0 afterEta = shifted at bodyStep
          cases bodyStep with
          | beta inner argument =>
              obtain ⟨original, rfl, originalEq⟩ := shift_eq_lam shiftedEq
              refine ⟨.lam original, ?_, .refl⟩
              rw [originalEq, subst_var_shift_cancel original 0]
          | appL _ functionStep =>
              subst shiftedEq
              obtain ⟨function', rfl, step'⟩ := betaStep_shift_inv functionStep
              exact ⟨function', .single (.eta function'), .single step'⟩
          | appR _ zeroStep => cases zeroStep
      | lam bodyStep' =>
          obtain ⟨meet, betaMeet, etaMeet⟩ := ih bodyStep'
          exact ⟨.lam meet, etaStar_lam betaMeet,
            reflGen_map _ (fun _ _ step => BetaStep.lam step) etaMeet⟩
  | @appL function function' argument functionStep ih =>
      cases etaStep with
      | appL _ functionStep' =>
          obtain ⟨meet, betaMeet, etaMeet⟩ := ih functionStep'
          exact ⟨.app meet argument, etaStar_appL _ betaMeet,
            reflGen_map (fun term => .app term argument)
              (fun _ _ step => BetaStep.appL argument step) etaMeet⟩
      | appR _ argumentStep =>
          exact ⟨.app function' _, .single (.appR _ argumentStep), .single (.appL _ functionStep)⟩
  | @appR function argument argument' argumentStep ih =>
      cases etaStep with
      | appL _ functionStep =>
          exact ⟨.app _ argument', .single (.appL _ functionStep), .single (.appR _ argumentStep)⟩
      | appR _ argumentStep' =>
          obtain ⟨meet, betaMeet, etaMeet⟩ := ih argumentStep'
          exact ⟨.app function meet, etaStar_appR _ betaMeet,
            reflGen_map (fun term => .app function term)
              (fun _ _ step => BetaStep.appR function step) etaMeet⟩

/-- Strip lemma: one β-step against many η-steps. -/
theorem beta_etaStar_strip {source afterBeta afterEta : LambdaTerm}
    (betaStep : BetaStep source afterBeta) (etaSteps : EtaStar source afterEta) :
    ∃ meet, EtaStar afterBeta meet ∧ Relation.ReflGen BetaStep afterEta meet := by
  induction etaSteps using Relation.ReflTransGen.head_induction_on generalizing afterBeta with
  | refl => exact ⟨afterBeta, .refl, .single betaStep⟩
  | head etaStep rest ih =>
      obtain ⟨meet, betaMeet, etaMeet⟩ := beta_eta_diagram betaStep etaStep
      cases etaMeet with
      | refl => exact ⟨_, betaMeet.trans rest, .refl⟩
      | single betaStep' =>
          obtain ⟨meet', betaMeet', etaMeet'⟩ := ih betaStep'
          exact ⟨meet', betaMeet.trans betaMeet', etaMeet'⟩

/-- **β-reduction and η-reduction commute.** -/
theorem betaStar_etaStar_commute {source afterBeta afterEta : LambdaTerm}
    (betaSteps : BetaStar source afterBeta) (etaSteps : EtaStar source afterEta) :
    ∃ meet, EtaStar afterBeta meet ∧ BetaStar afterEta meet := by
  induction betaSteps generalizing afterEta with
  | refl => exact ⟨afterEta, etaSteps, .refl⟩
  | tail _ betaStep ih =>
      obtain ⟨middle, betaMiddle, etaMiddle⟩ := ih etaSteps
      obtain ⟨meet, betaMeet, middleMeet⟩ := beta_etaStar_strip betaStep betaMiddle
      exact ⟨meet, betaMeet, etaMiddle.trans middleMeet.to_reflTransGen⟩

/-! ## βη is confluent -/

/-- One βη-step. -/
def BetaEtaStep (source target : LambdaTerm) : Prop :=
  BetaStep source target ∨ EtaStep source target

/-- Many βη-steps. -/
abbrev BetaEtaStar := Relation.ReflTransGen BetaEtaStep

/-- βη-conversion. -/
def BetaEtaConv (left right : LambdaTerm) : Prop := Relation.EqvGen BetaEtaStep left right

theorem betaEtaStar_of_betaStar {source target : LambdaTerm} (reduces : BetaStar source target) :
    BetaEtaStar source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Or.inl step)

theorem betaEtaStar_of_etaStar {source target : LambdaTerm} (reduces : EtaStar source target) :
    BetaEtaStar source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Or.inr step)

/-- Either many β-steps or many η-steps. -/
def BetaOrEtaStar (source target : LambdaTerm) : Prop :=
  BetaStar source target ∨ EtaStar source target

theorem betaOrEtaStar_diamond {source left right : LambdaTerm}
    (toLeft : BetaOrEtaStar source left) (toRight : BetaOrEtaStar source right) :
    ∃ meet, BetaOrEtaStar left meet ∧ BetaOrEtaStar right meet := by
  rcases toLeft with betaLeft | etaLeft <;> rcases toRight with betaRight | etaRight
  · obtain ⟨meet, leftMeet, rightMeet⟩ := betaStar_confluent betaLeft betaRight
    exact ⟨meet, Or.inl leftMeet, Or.inl rightMeet⟩
  · obtain ⟨meet, leftMeet, rightMeet⟩ := betaStar_etaStar_commute betaLeft etaRight
    exact ⟨meet, Or.inr leftMeet, Or.inl rightMeet⟩
  · obtain ⟨meet, rightMeet, leftMeet⟩ := betaStar_etaStar_commute betaRight etaLeft
    exact ⟨meet, Or.inl leftMeet, Or.inr rightMeet⟩
  · obtain ⟨meet, leftMeet, rightMeet⟩ := etaStar_confluent etaLeft etaRight
    exact ⟨meet, Or.inr leftMeet, Or.inr rightMeet⟩

theorem betaEtaStar_iff {source target : LambdaTerm} :
    BetaEtaStar source target ↔ Relation.ReflTransGen BetaOrEtaStar source target := by
  constructor
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih =>
        exact ih.tail (step.elim (fun beta => Or.inl (.single beta))
          (fun eta => Or.inr (.single eta)))
  · intro reduces
    induction reduces with
    | refl => exact .refl
    | tail _ step ih =>
        exact ih.trans (step.elim betaEtaStar_of_betaStar betaEtaStar_of_etaStar)

/-- **βη-reduction is confluent** (Hindley–Rosen). -/
theorem betaEtaStar_confluent {source left right : LambdaTerm}
    (toLeft : BetaEtaStar source left) (toRight : BetaEtaStar source right) :
    Relation.Join BetaEtaStar left right := by
  obtain ⟨meet, leftMeet, rightMeet⟩ := Relation.church_rosser (r := BetaOrEtaStar)
    (fun _ _ _ leftStep rightStep =>
      let ⟨meet, leftMeet, rightMeet⟩ := betaOrEtaStar_diamond leftStep rightStep
      ⟨meet, .single leftMeet, .single rightMeet⟩)
    (betaEtaStar_iff.mp toLeft) (betaEtaStar_iff.mp toRight)
  exact ⟨meet, betaEtaStar_iff.mpr leftMeet, betaEtaStar_iff.mpr rightMeet⟩

/-- **βη-convertible terms have a common βη-reduct.** -/
theorem join_of_betaEtaConv {left right : LambdaTerm} (convertible : BetaEtaConv left right) :
    Relation.Join BetaEtaStar left right := by
  induction convertible with
  | rel first second step => exact ⟨second, .single step, .refl⟩
  | refl term => exact ⟨term, .refl, .refl⟩
  | symm _ _ _ ih =>
      obtain ⟨meet, firstMeet, secondMeet⟩ := ih
      exact ⟨meet, secondMeet, firstMeet⟩
  | trans _ _ _ _ _ firstIh secondIh =>
      obtain ⟨meet, firstMeet, middleMeet⟩ := firstIh
      obtain ⟨meet', middleMeet', lastMeet⟩ := secondIh
      obtain ⟨common, meetCommon, meetCommon'⟩ := betaEtaStar_confluent middleMeet middleMeet'
      exact ⟨common, firstMeet.trans meetCommon, lastMeet.trans meetCommon'⟩

end Mettapedia.GSLT.GraphTheory.BetaEta
