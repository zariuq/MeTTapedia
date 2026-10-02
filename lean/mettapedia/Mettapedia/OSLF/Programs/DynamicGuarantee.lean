import Mettapedia.OSLF.Programs.GradualGuarantee

/-!
# The dynamic gradual guarantee, with evidence as meets

A run-time semantics for the gradually typed λ-calculus of
`GradualGuarantee`, in the style of the evidence semantics of Abstracting
Gradual Typing.  For consistent equality, evidence combines by meets (the
erratum's Proposition 5), so a value carries as its evidence the meet of the
types it has been checked against:
* numbers and booleans carry `Int` and `Bool`;
* a closure carries an arrow `E₁ → E₂`, starting at its static type
  `A → B` and refined by every cast (`castTo`).

**Run-time checks** (`eval`): an ascription `t :: G` meets the evidence of the
value with `G`; an application meets the argument's evidence with the
function's domain evidence and the result's with its codomain evidence; a
conditional meets the chosen branch's value with the join type of the two
branches; addition needs numbers.  A failed meet is a run-time error.  Types
needed at run time come from the syntax-directed type inference `infer`,
which is exactly the typing relation (`infer_iff`).

The evaluator is indexed by fuel: `eval n` returns `none` when fuel runs out,
`some none` on a run-time error, and `some (some v)` on a value.

**The dynamic gradual guarantee.**  If `t ⊑ t'` (less precise annotations in
`t'`), in related environments:
* if `t` evaluates to `v`, then `t'` evaluates to some `v'` with `v ⊑ v'`, with
  the same fuel (`dynamic_gradual_guarantee_value`);
* if `t'` evaluates to `v'`, then `t` evaluates to some `v ⊑ v'` or fails with
  a run-time error (`dynamic_gradual_guarantee_error`).
The proof rests on monotonicity of the meet (`meet_mono`), the same fact
behind the static guarantee.

**Soundness of the semantics** (`eval_sound`): every value a well-typed program
computes has evidence refining its static type (`ValTyped`); in particular a
closure's evidence stays below its annotation and body type.

**Annotation erasure** (`erase`, every annotation replaced by `?`) is a
precision step (`termPrec_erase`), so the guarantee specialises to the two
halves of a typing property for run-time behaviour: erasing annotations never
changes a number or boolean the program computes (`erase_preserves_num`,
`erase_preserves_bool`), and an annotated program either computes what its
erasure computes or fails with a run-time error, never something else
(`annotated_agrees_or_fails`).

Controls: the semantics does detect errors (`Controls.cast_error`,
`Controls.domain_error`, `Controls.codomain_error`), and the error case of the
guarantee is inhabited: a more precise program can fail where the less precise
one succeeds (`Controls.more_precise_fails`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Programs.DynamicGuarantee

open Mettapedia.OSLF.Programs.GradualTypes
open Mettapedia.OSLF.Programs.GradualGuarantee

/-! ## Type inference -/

/-- Consistency, decided through the meet. -/
def consisB (A B : GType) : Bool :=
  (meet A B).isSome

theorem consisB_iff {A B : GType} : consisB A B = true ↔ Consis A B := by
  rw [consisB, Option.isSome_iff_exists]
  exact meet_isSome_iff

/-- **Syntax-directed type inference.** -/
def infer : List GType → Term → Option GType
  | Γ, .var i => Γ[i]?
  | _, .num _ => some .int
  | _, .bool _ => some .bool
  | Γ, .add a b =>
    match infer Γ a, infer Γ b with
    | some A, some B => if consisB A .int && consisB B .int then some .int else none
    | _, _ => none
  | Γ, .ite c t e =>
    match infer Γ c, infer Γ t, infer Γ e with
    | some C, some A, some B => if consisB C .bool then meet A B else none
    | _, _, _ => none
  | Γ, .lam A body => (infer (A :: Γ) body).map (.arr A)
  | Γ, .app f a =>
    match infer Γ f, infer Γ a with
    | some F, some A =>
      match dom F, cod F with
      | some D, some C => if consisB A D then some C else none
      | _, _ => none
    | _, _ => none
  | Γ, .asc t G =>
    match infer Γ t with
    | some A => if consisB A G then some G else none
    | none => none

theorem infer_sound : ∀ {Γ : List GType} {t : Term} {A : GType}, infer Γ t = some A →
    HasType Γ t A
  | Γ, .var i, A, h => .var h
  | _, .num _, A, h => by cases h; exact .num _ _
  | _, .bool _, A, h => by cases h; exact .bool _ _
  | Γ, .add a b, A, h => by
      simp only [infer] at h
      rcases ha : infer Γ a with _ | A₁ <;> rcases hb : infer Γ b with _ | B₁ <;>
        simp only [ha, hb, reduceCtorEq] at h
      split at h
      · rename_i hc
        cases h
        rw [Bool.and_eq_true, consisB_iff, consisB_iff] at hc
        exact .add (infer_sound ha) (infer_sound hb) hc.1 hc.2
      · cases h
  | Γ, .ite c t e, A, h => by
      simp only [infer] at h
      rcases hc : infer Γ c with _ | C <;> rcases ht : infer Γ t with _ | A₁ <;>
        rcases he : infer Γ e with _ | B₁ <;> simp only [hc, ht, he, reduceCtorEq] at h
      split at h
      · rename_i hC
        exact .ite (infer_sound hc) (consisB_iff.mp hC) (infer_sound ht) (infer_sound he) h
      · cases h
  | Γ, .lam A₀ body, A, h => by
      simp only [infer] at h
      rcases hb : infer (A₀ :: Γ) body with _ | B
      · simp [hb] at h
      · simp only [hb, Option.map_some, Option.some.injEq] at h
        subst h
        exact .lam (infer_sound hb)
  | Γ, .app f a, A, h => by
      simp only [infer] at h
      rcases hf : infer Γ f with _ | F <;> rcases ha : infer Γ a with _ | A₁ <;>
        simp only [hf, ha, reduceCtorEq] at h
      rcases hd : dom F with _ | D <;> rcases hcd : cod F with _ | C <;>
        simp only [hd, hcd, reduceCtorEq] at h
      split at h
      · rename_i hAD
        cases h
        exact .app (infer_sound hf) (infer_sound ha) hd (consisB_iff.mp hAD) hcd
      · cases h
  | Γ, .asc t G, A, h => by
      simp only [infer] at h
      rcases ht : infer Γ t with _ | A₁ <;> simp only [ht, reduceCtorEq] at h
      split at h
      · rename_i hAG
        cases h
        exact .asc (infer_sound ht) (consisB_iff.mp hAG)
      · cases h

theorem infer_complete {Γ : List GType} {t : Term} {A : GType} (typed : HasType Γ t A) :
    infer Γ t = some A := by
  induction typed with
  | var h => exact h
  | num => rfl
  | bool => rfl
  | add _ _ hA hB iha ihb =>
    simp only [infer, iha, ihb, consisB_iff.mpr hA, consisB_iff.mpr hB, Bool.and_self,
      if_true]
  | ite _ hC _ _ hM ihc iht ihe =>
    simp only [infer, ihc, iht, ihe, consisB_iff.mpr hC, if_true, hM]
  | lam _ ih => simp only [infer, ih, Option.map_some]
  | app _ _ hD hAD hC ihf iha =>
    simp only [infer, ihf, iha, hD, hC, consisB_iff.mpr hAD, if_true]
  | asc _ hAB ih => simp only [infer, ih, consisB_iff.mpr hAB, if_true]

/-- **Type inference is the typing relation.** -/
theorem infer_iff {Γ : List GType} {t : Term} {A : GType} : infer Γ t = some A ↔ HasType Γ t A :=
  ⟨infer_sound, infer_complete⟩

/-- Inference is monotone for precision (the static guarantee). -/
theorem infer_mono {Γ Γ' : List GType} {t t' : Term} {A : GType} (h : infer Γ t = some A)
    (hΓ : List.Forall₂ Prec Γ Γ') (ht : TermPrec t t') :
    ∃ A', infer Γ' t' = some A' ∧ Prec A A' := by
  obtain ⟨A', typed, prec⟩ := static_gradual_guarantee (infer_sound h) hΓ ht
  exact ⟨A', infer_complete typed, prec⟩

/-! ## Values with evidence -/

/-- Run-time values.  A closure records its static context and environment,
its annotation and body, and its evidence `E₁ → E₂`. -/
inductive Val where
  | num (value : Nat)
  | bool (value : Bool)
  | clo (types : List GType) (env : List Val) (annotation : GType) (body : Term)
      (domain codomain : GType)

/-- **Casting a value**: meet its evidence with the target type. -/
def castTo : Val → GType → Option Val
  | .num k, G => (meet .int G).map fun _ => .num k
  | .bool b, G => (meet .bool G).map fun _ => .bool b
  | .clo Γ ρ A body E₁ E₂, G =>
    match meet (.arr E₁ E₂) G with
    | some (.arr M₁ M₂) => some (.clo Γ ρ A body M₁ M₂)
    | _ => none

/-- **Evaluation with evidence**, by fuel: `none` when the fuel runs out,
`some none` on a run-time error. -/
def eval : Nat → List GType → List Val → Term → Option (Option Val)
  | 0, _, _, _ => none
  | _ + 1, _, ρ, .var i => some ρ[i]?
  | _ + 1, _, _, .num k => some (some (.num k))
  | _ + 1, _, _, .bool b => some (some (.bool b))
  | n + 1, Γ, ρ, .add a b =>
    match eval n Γ ρ a, eval n Γ ρ b with
    | some (some (.num x)), some (some (.num y)) => some (some (.num (x + y)))
    | some _, some _ => some none
    | _, _ => none
  | n + 1, Γ, ρ, .ite c t e =>
    match eval n Γ ρ c with
    | some (some (.bool b)) =>
      match infer Γ t, infer Γ e with
      | some A, some B =>
        match meet A B with
        | some M =>
          match eval n Γ ρ (if b then t else e) with
          | some (some v) => some (castTo v M)
          | some none => some none
          | none => none
        | none => some none
      | _, _ => some none
    | some _ => some none
    | none => none
  | _ + 1, Γ, ρ, .lam A body =>
    match infer (A :: Γ) body with
    | some B => some (some (.clo Γ ρ A body A B))
    | none => some none
  | n + 1, Γ, ρ, .app f a =>
    match eval n Γ ρ f, eval n Γ ρ a with
    | some (some (.clo cΓ cρ A body E₁ E₂)), some (some v) =>
      match castTo v E₁ with
      | some v' =>
        match eval n (A :: cΓ) (v' :: cρ) body with
        | some (some w) => some (castTo w E₂)
        | some none => some none
        | none => none
      | none => some none
    | some _, some _ => some none
    | _, _ => none
  | n + 1, Γ, ρ, .asc t G =>
    match eval n Γ ρ t with
    | some (some v) => some (castTo v G)
    | some none => some none
    | none => none

/-! ## Precision of values -/

mutual
/-- Precision of values: the same value with less precise evidence and
annotations. -/
inductive ValPrec : Val → Val → Prop
  | num (k : Nat) : ValPrec (.num k) (.num k)
  | bool (b : Bool) : ValPrec (.bool b) (.bool b)
  | clo {Γ Γ' : List GType} {ρ ρ' : List Val} {A A' E₁ E₂ E₁' E₂' : GType} {body body' : Term} :
      List.Forall₂ Prec Γ Γ' → EnvPrec ρ ρ' → Prec A A' → TermPrec body body' →
        Prec E₁ E₁' → Prec E₂ E₂' →
          ValPrec (.clo Γ ρ A body E₁ E₂) (.clo Γ' ρ' A' body' E₁' E₂')

/-- Precision of environments, entry by entry. -/
inductive EnvPrec : List Val → List Val → Prop
  | nil : EnvPrec [] []
  | cons {v v' : Val} {ρ ρ' : List Val} : ValPrec v v' → EnvPrec ρ ρ' → EnvPrec (v :: ρ) (v' :: ρ')
end

theorem EnvPrec.getElem? : ∀ {ρ ρ' : List Val}, EnvPrec ρ ρ' → ∀ i : Nat,
    (ρ[i]? = none ∧ ρ'[i]? = none) ∨ ∃ v v', ρ[i]? = some v ∧ ρ'[i]? = some v' ∧ ValPrec v v'
  | _, _, .nil, _ => Or.inl ⟨rfl, rfl⟩
  | _, _, .cons hv _, 0 => Or.inr ⟨_, _, rfl, rfl, hv⟩
  | _, _, .cons _ rest, i + 1 => by
      simp only [List.getElem?_cons_succ]
      exact rest.getElem? i

/-- A meet with an arrow is an arrow. -/
theorem meet_arr_left {E₁ E₂ G M : GType} (h : meet (.arr E₁ E₂) G = some M) :
    ∃ M₁ M₂, M = .arr M₁ M₂ := by
  cases G with
  | unknown => cases h; exact ⟨_, _, rfl⟩
  | int => cases h
  | bool => cases h
  | arr G₁ G₂ =>
    obtain ⟨M₁, M₂, _, _, rfl⟩ := meet_arr_eq_some.mp h
    exact ⟨M₁, M₂, rfl⟩

theorem castTo_clo_eq_some {Γ : List GType} {ρ : List Val} {A E₁ E₂ G : GType} {body : Term}
    {w : Val} (h : castTo (.clo Γ ρ A body E₁ E₂) G = some w) :
    ∃ M₁ M₂, meet (.arr E₁ E₂) G = some (.arr M₁ M₂) ∧ w = .clo Γ ρ A body M₁ M₂ := by
  simp only [castTo] at h
  rcases hm : meet (.arr E₁ E₂) G with _ | M
  · simp [hm] at h
  · obtain ⟨M₁, M₂, rfl⟩ := meet_arr_left hm
    simp only [hm, Option.some.injEq] at h
    exact ⟨M₁, M₂, rfl, h.symm⟩

/-- **A cast that succeeds on a value succeeds on every less precise value,
towards every less precise type.** -/
theorem castTo_mono {v v' w : Val} {G G' : GType} (h : castTo v G = some w) (hv : ValPrec v v')
    (hG : Prec G G') : ∃ w', castTo v' G' = some w' ∧ ValPrec w w' := by
  cases hv with
  | num k =>
    simp only [castTo, Option.map_eq_some_iff] at h
    obtain ⟨M, hM, rfl⟩ := h
    obtain ⟨M', hM', _⟩ := meet_mono hM (Prec.refl _) hG
    exact ⟨.num k, by simp [castTo, hM'], .num k⟩
  | bool b =>
    simp only [castTo, Option.map_eq_some_iff] at h
    obtain ⟨M, hM, rfl⟩ := h
    obtain ⟨M', hM', _⟩ := meet_mono hM (Prec.refl _) hG
    exact ⟨.bool b, by simp [castTo, hM'], .bool b⟩
  | clo hΓ hρ hA hbody hE₁ hE₂ =>
    obtain ⟨M₁, M₂, hM, rfl⟩ := castTo_clo_eq_some h
    obtain ⟨M', hM', hMM'⟩ := meet_mono hM (.arr hE₁ hE₂) hG
    obtain ⟨M₁', M₂', rfl⟩ := meet_arr_left hM'
    cases hMM' with
    | arr h₁ h₂ =>
      exact ⟨_, by simp only [castTo, hM'], .clo hΓ hρ hA hbody h₁ h₂⟩

/-- **A cast that succeeds on a less precise value either fails on a more
precise value or succeeds with a more precise result.** -/
theorem castTo_reflect {v v' w' : Val} {G G' : GType} (h' : castTo v' G' = some w')
    (hv : ValPrec v v') (hG : Prec G G') :
    castTo v G = none ∨ ∃ w, castTo v G = some w ∧ ValPrec w w' := by
  rcases hc : castTo v G with _ | w
  · exact Or.inl rfl
  · right
    obtain ⟨w'', h'', hw⟩ := castTo_mono hc hv hG
    rw [h'] at h''
    cases h''
    exact ⟨w, rfl, hw⟩

/-! ## The dynamic gradual guarantee -/

/-- The joint precision hypotheses of the guarantee. -/
structure Related (Γ Γ' : List GType) (ρ ρ' : List Val) (t t' : Term) : Prop where
  types : List.Forall₂ Prec Γ Γ'
  env : EnvPrec ρ ρ'
  term : TermPrec t t'

/-- **Dynamic gradual guarantee, value part.**  If a program evaluates to a
value, a less precise program evaluates, with the same fuel, to a less precise
value. -/
theorem dynamic_gradual_guarantee_value : ∀ (n : Nat) {Γ Γ' : List GType} {ρ ρ' : List Val}
    {t t' : Term} {v : Val}, Related Γ Γ' ρ ρ' t t' → eval n Γ ρ t = some (some v) →
      ∃ v', eval n Γ' ρ' t' = some (some v') ∧ ValPrec v v'
  | 0, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, Γ, Γ', ρ, ρ', t, t', v, ⟨hΓ, hρ, ht⟩, h => by
    cases ht with
    | var i =>
      simp only [eval, Option.some.injEq] at h ⊢
      rcases hρ.getElem? i with ⟨hnone, _⟩ | ⟨w, w', hw, hw', hww'⟩
      · rw [hnone] at h; cases h
      · rw [hw] at h
        cases h
        exact ⟨w', hw', hww'⟩
    | num k =>
      simp only [eval, Option.some.injEq] at h ⊢
      cases h
      exact ⟨_, rfl, .num k⟩
    | bool b =>
      simp only [eval, Option.some.injEq] at h ⊢
      cases h
      exact ⟨_, rfl, .bool b⟩
    | @add a b a' b' ha hb =>
      simp only [eval] at h ⊢
      rcases ea : eval n Γ ρ a with _ | _ | va <;> rcases eb : eval n Γ ρ b with _ | _ | vb <;>
        simp only [ea, eb, reduceCtorEq, Option.some.injEq] at h
      cases va <;> cases vb <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨va', ea', pa⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, ha⟩ ea
      obtain ⟨vb', eb', pb⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, hb⟩ eb
      cases pa
      cases pb
      exact ⟨_, by simp only [ea', eb'], .num _⟩
    | @ite c th el c' th' el' hc hth hel =>
      simp only [eval] at h ⊢
      rcases ec : eval n Γ ρ c with _ | _ | vc <;> simp only [ec, reduceCtorEq, Option.some.injEq] at h
      cases vc with
      | bool bc =>
        simp only at h
        obtain ⟨vc', ec', pc⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, hc⟩ ec
        cases pc
        rcases it : infer Γ th with _ | A <;> rcases ie : infer Γ el with _ | B <;>
          simp only [it, ie, reduceCtorEq, Option.some.injEq] at h
        rcases hm : meet A B with _ | M <;> simp only [hm, reduceCtorEq, Option.some.injEq] at h
        obtain ⟨A', it', pA⟩ := infer_mono it hΓ hth
        obtain ⟨B', ie', pB⟩ := infer_mono ie hΓ hel
        obtain ⟨M', hm', pM⟩ := meet_mono hm pA pB
        have hbranch : TermPrec (if bc then th else el) (if bc then th' else el') := by
          cases bc
          · exact hel
          · exact hth
        rcases eb : eval n Γ ρ (if bc then th else el) with _ | _ | w <;>
          simp only [eb, reduceCtorEq, Option.some.injEq] at h
        obtain ⟨w', eb', pw⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, hbranch⟩ eb
        obtain ⟨u', hu', pu⟩ := castTo_mono h pw pM
        exact ⟨u', by simp only [ec', it', ie', hm', eb', hu'], pu⟩
      | num _ => simp at h
      | clo _ _ _ _ _ _ => simp at h
    | @lam A A' body body' hA hbody =>
      simp only [eval] at h ⊢
      rcases ib : infer (A :: Γ) body with _ | B <;> simp only [ib, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨B', ib', pB⟩ := infer_mono ib (.cons hA hΓ) hbody
      exact ⟨_, by simp only [ib'], .clo hΓ hρ hA hbody hA pB⟩
    | @app f a f' a' hf ha =>
      simp only [eval] at h ⊢
      rcases ef : eval n Γ ρ f with _ | _ | vf <;> rcases ea : eval n Γ ρ a with _ | _ | va <;>
        simp only [ef, ea, reduceCtorEq, Option.some.injEq] at h
      cases vf with
      | clo cΓ cρ A body E₁ E₂ =>
        simp only at h
        obtain ⟨vf', ef', pf⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, hf⟩ ef
        obtain ⟨va', ea', pa⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, ha⟩ ea
        cases pf with
        | clo hcΓ hcρ hA hbody hE₁ hE₂ =>
          rcases hcast : castTo va E₁ with _ | u <;> simp only [hcast, reduceCtorEq, Option.some.injEq] at h
          obtain ⟨u', hcast', pu⟩ := castTo_mono hcast pa hE₁
          rcases eb : eval n (A :: cΓ) (u :: cρ) body with _ | _ | w <;>
            simp only [eb, reduceCtorEq, Option.some.injEq] at h
          obtain ⟨w', eb', pw⟩ :=
            dynamic_gradual_guarantee_value n ⟨.cons hA hcΓ, .cons pu hcρ, hbody⟩ eb
          obtain ⟨r', hr', pr⟩ := castTo_mono h pw hE₂
          exact ⟨r', by simp only [ef', ea', hcast', eb', hr'], pr⟩
      | num _ => simp at h
      | bool _ => simp at h
    | @asc s s' G G' hs hG =>
      simp only [eval] at h ⊢
      rcases es : eval n Γ ρ s with _ | _ | w <;> simp only [es, reduceCtorEq, Option.some.injEq] at h
      obtain ⟨w', es', pw⟩ := dynamic_gradual_guarantee_value n ⟨hΓ, hρ, hs⟩ es
      obtain ⟨u', hu', pu⟩ := castTo_mono h pw hG
      exact ⟨u', by simp only [es', hu'], pu⟩

/-- **Dynamic gradual guarantee, error part.**  If a less precise program
evaluates to a value, the more precise program evaluates, with the same fuel,
to a more precise value or to a run-time error. -/
theorem dynamic_gradual_guarantee_error : ∀ (n : Nat) {Γ Γ' : List GType} {ρ ρ' : List Val}
    {t t' : Term} {v' : Val}, Related Γ Γ' ρ ρ' t t' → eval n Γ' ρ' t' = some (some v') →
      eval n Γ ρ t = some none ∨ ∃ v, eval n Γ ρ t = some (some v) ∧ ValPrec v v'
  | 0, _, _, _, _, _, _, _, _, h => by cases h
  | n + 1, Γ, Γ', ρ, ρ', t, t', v', ⟨hΓ, hρ, ht⟩, h => by
    cases ht with
    | var i =>
      simp only [eval, Option.some.injEq] at h ⊢
      rcases hρ.getElem? i with ⟨_, hnone⟩ | ⟨w, w', hw, hw', hww'⟩
      · rw [hnone] at h; cases h
      · rw [hw', Option.some.injEq] at h
        subst h
        exact Or.inr ⟨w, hw, hww'⟩
    | num k =>
      simp only [eval, Option.some.injEq] at h ⊢
      cases h
      exact Or.inr ⟨_, rfl, .num k⟩
    | bool b =>
      simp only [eval, Option.some.injEq] at h ⊢
      cases h
      exact Or.inr ⟨_, rfl, .bool b⟩
    | @add a b a' b' ha hb =>
      simp only [eval] at h ⊢
      rcases ea' : eval n Γ' ρ' a' with _ | _ | va' <;> rcases eb' : eval n Γ' ρ' b' with _ | _ | vb' <;>
        simp only [ea', eb', reduceCtorEq, Option.some.injEq] at h
      cases va' <;> cases vb' <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, ha⟩ ea' with ea | ⟨va, ea, pa⟩ <;>
      rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, hb⟩ eb' with eb | ⟨vb, eb, pb⟩
      · exact Or.inl (by simp only [ea, eb])
      · exact Or.inl (by simp only [ea, eb])
      · exact Or.inl (by cases pa; simp only [ea, eb])
      · cases pa
        cases pb
        exact Or.inr ⟨_, by simp only [ea, eb], .num _⟩
    | @ite c th el c' th' el' hc hth hel =>
      simp only [eval] at h ⊢
      rcases ec' : eval n Γ' ρ' c' with _ | _ | vc' <;>
        simp only [ec', reduceCtorEq, Option.some.injEq] at h
      cases vc' with
      | bool bc =>
        simp only at h
        rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, hc⟩ ec' with ec | ⟨vc, ec, pc⟩
        · exact Or.inl (by simp only [ec])
        · cases pc
          rcases it : infer Γ th with _ | A <;> rcases ie : infer Γ el with _ | B
          · exact Or.inl (by simp only [ec])
          · exact Or.inl (by simp only [ec])
          · exact Or.inl (by simp only [ec])
          · rcases hm : meet A B with _ | M
            · exact Or.inl (by simp only [ec, hm])
            · obtain ⟨A', it', pA⟩ := infer_mono it hΓ hth
              obtain ⟨B', ie', pB⟩ := infer_mono ie hΓ hel
              obtain ⟨M', hm', pM⟩ := meet_mono hm pA pB
              simp only [it', ie', hm'] at h
              have hbranch : TermPrec (if bc then th else el) (if bc then th' else el') := by
                cases bc
                · exact hel
                · exact hth
              rcases eb' : eval n Γ' ρ' (if bc then th' else el') with _ | _ | w' <;>
                simp only [eb', reduceCtorEq, Option.some.injEq] at h
              rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, hbranch⟩ eb' with
                eb | ⟨w, eb, pw⟩
              · exact Or.inl (by simp only [ec, hm, eb])
              · rcases castTo_reflect h pw pM with hnone | ⟨u, hu, pu⟩
                · exact Or.inl (by simp only [ec, hm, eb, hnone])
                · exact Or.inr ⟨u, by simp only [ec, hm, eb, hu], pu⟩
      | num _ => simp at h
      | clo _ _ _ _ _ _ => simp at h
    | @lam A A' body body' hA hbody =>
      simp only [eval] at h ⊢
      rcases ib : infer (A :: Γ) body with _ | B
      · exact Or.inl rfl
      · simp only [Option.some.injEq]
        obtain ⟨B', ib', pB⟩ := infer_mono ib (.cons hA hΓ) hbody
        simp only [ib', Option.some.injEq] at h
        subst h
        exact Or.inr ⟨_, rfl, .clo hΓ hρ hA hbody hA pB⟩
    | @app f a f' a' hf ha =>
      simp only [eval] at h ⊢
      rcases ef' : eval n Γ' ρ' f' with _ | _ | vf' <;>
        rcases ea' : eval n Γ' ρ' a' with _ | _ | va' <;>
        simp only [ef', ea', reduceCtorEq, Option.some.injEq] at h
      cases vf' with
      | clo cΓ' cρ' A' body' E₁' E₂' =>
        simp only at h
        rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, hf⟩ ef' with ef | ⟨vf, ef, pf⟩ <;>
        rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, ha⟩ ea' with ea | ⟨va, ea, pa⟩
        · exact Or.inl (by simp only [ef, ea])
        · exact Or.inl (by simp only [ef, ea])
        · exact Or.inl (by cases pf; simp only [ef, ea])
        · cases pf with
          | clo hcΓ hcρ hA hbody hE₁ hE₂ =>
            rename_i cΓ cρ A body E₁ E₂
            rcases hcast' : castTo va' E₁' with _ | u' <;>
              simp only [hcast', reduceCtorEq, Option.some.injEq] at h
            rcases castTo_reflect hcast' pa hE₁ with hnone | ⟨u, hcast, pu⟩
            · exact Or.inl (by simp only [ef, ea, hnone])
            · rcases eb' : eval n (A' :: cΓ') (u' :: cρ') body' with _ | _ | w' <;>
                simp only [eb', reduceCtorEq, Option.some.injEq] at h
              rcases dynamic_gradual_guarantee_error n ⟨.cons hA hcΓ, .cons pu hcρ, hbody⟩ eb' with
                eb | ⟨w, eb, pw⟩
              · exact Or.inl (by simp only [ef, ea, hcast, eb])
              · rcases castTo_reflect h pw hE₂ with hnone | ⟨r, hr, pr⟩
                · exact Or.inl (by simp only [ef, ea, hcast, eb, hnone])
                · exact Or.inr ⟨r, by simp only [ef, ea, hcast, eb, hr], pr⟩
      | num _ => simp at h
      | bool _ => simp at h
    | @asc s s' G G' hs hG =>
      simp only [eval] at h ⊢
      rcases es' : eval n Γ' ρ' s' with _ | _ | w' <;>
        simp only [es', reduceCtorEq, Option.some.injEq] at h
      rcases dynamic_gradual_guarantee_error n ⟨hΓ, hρ, hs⟩ es' with es | ⟨w, es, pw⟩
      · exact Or.inl (by simp only [es])
      · simp only [es, Option.some.injEq]
        rcases castTo_reflect h pw hG with hnone | ⟨u, hu, pu⟩
        · exact Or.inl hnone
        · exact Or.inr ⟨u, hu, pu⟩

/-! ## Soundness: evidence refines the static type -/

mutual
/-- A value whose evidence refines a static type. -/
inductive ValTyped : Val → GType → Prop
  | num {k : Nat} {G : GType} : Prec .int G → ValTyped (.num k) G
  | bool {b : Bool} {G : GType} : Prec .bool G → ValTyped (.bool b) G
  | clo {cΓ : List GType} {cρ : List Val} {A E₁ E₂ B G : GType} {body : Term} :
      EnvTyped cρ cΓ → HasType (A :: cΓ) body B → Prec E₁ A → Prec E₂ B →
        Prec (.arr E₁ E₂) G → ValTyped (.clo cΓ cρ A body E₁ E₂) G

/-- An environment whose values are typed by a context. -/
inductive EnvTyped : List Val → List GType → Prop
  | nil : EnvTyped [] []
  | cons {v : Val} {A : GType} {ρ : List Val} {Γ : List GType} :
      ValTyped v A → EnvTyped ρ Γ → EnvTyped (v :: ρ) (A :: Γ)
end

theorem ValTyped.mono {v : Val} {G G' : GType} (typed : ValTyped v G) (prec : Prec G G') :
    ValTyped v G' := by
  cases typed with
  | num h => exact .num (h.trans prec)
  | bool h => exact .bool (h.trans prec)
  | clo henv hbody h₁ h₂ harr => exact .clo henv hbody h₁ h₂ (harr.trans prec)

theorem EnvTyped.getElem? : ∀ {ρ : List Val} {Γ : List GType}, EnvTyped ρ Γ →
    ∀ {i : Nat} {A : GType}, Γ[i]? = some A → ∃ v, ρ[i]? = some v ∧ ValTyped v A
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hv _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, hv⟩
  | _, _, .cons _ rest, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact rest.getElem? h

/-- Only `Int` and `?` are above `Int` in precision. -/
theorem prec_of_meet_base {B G M : GType} (base : B = .int ∨ B = .bool)
    (h : meet B G = some M) : Prec B G := by
  have below := ((prec_meet_iff h M).mp (Prec.refl M))
  rcases base with rfl | rfl
  · cases below.1
    exact below.2
  · cases below.1
    exact below.2

/-- **A cast keeps a value typed**, at the target type. -/
theorem castTo_typed {v w : Val} {A G : GType} (typed : ValTyped v A) (h : castTo v G = some w) :
    ValTyped w G := by
  cases typed with
  | num _ =>
    simp only [castTo, Option.map_eq_some_iff] at h
    obtain ⟨M, hM, rfl⟩ := h
    exact .num (prec_of_meet_base (Or.inl rfl) hM)
  | bool _ =>
    simp only [castTo, Option.map_eq_some_iff] at h
    obtain ⟨M, hM, rfl⟩ := h
    exact .bool (prec_of_meet_base (Or.inr rfl) hM)
  | clo henv hbody h₁ h₂ _ =>
    obtain ⟨M₁, M₂, hM, rfl⟩ := castTo_clo_eq_some h
    have below := (prec_meet_iff hM (.arr M₁ M₂)).mp (Prec.refl _)
    cases below.1 with
    | arr p₁ p₂ => exact .clo henv hbody (p₁.trans h₁) (p₂.trans h₂) below.2

theorem cod_bound {E₁ E₂ F C : GType} (prec : Prec (.arr E₁ E₂) F) (h : cod F = some C) :
    Prec E₂ C := by
  cases prec with
  | unknown => cases h; exact .unknown _
  | arr _ p₂ => cases h; exact p₂

/-- **Soundness of the evidence semantics**: a value computed by a well-typed
program has evidence refining its static type. -/
theorem eval_sound : ∀ (n : Nat) {Γ : List GType} {ρ : List Val} {t : Term} {A : GType} {v : Val},
    HasType Γ t A → EnvTyped ρ Γ → eval n Γ ρ t = some (some v) → ValTyped v A
  | 0, _, _, _, _, _, _, _, h => by cases h
  | n + 1, Γ, ρ, t, A, v, typed, henv, h => by
    cases typed with
    | var hA =>
      simp only [eval, Option.some.injEq] at h
      obtain ⟨w, hw, typedw⟩ := henv.getElem? hA
      rw [hw, Option.some.injEq] at h
      exact h ▸ typedw
    | num => simp only [eval, Option.some.injEq] at h; subst h; exact .num (Prec.refl _)
    | bool => simp only [eval, Option.some.injEq] at h; subst h; exact .bool (Prec.refl _)
    | @add _ a b _ _ _ _ _ _ =>
      simp only [eval] at h
      rcases ea : eval n Γ ρ a with _ | _ | va <;> rcases eb : eval n Γ ρ b with _ | _ | vb <;>
        simp only [ea, eb, reduceCtorEq, Option.some.injEq] at h
      cases va <;> cases vb <;> simp only [reduceCtorEq, Option.some.injEq] at h
      subst h
      exact .num (Prec.refl _)
    | @ite _ c th el C A₁ B₁ M tc _ tt te hM =>
      simp only [eval] at h
      rcases ec : eval n Γ ρ c with _ | _ | vc <;> simp only [ec, reduceCtorEq, Option.some.injEq] at h
      cases vc with
      | bool bc =>
        simp only [infer_complete tt, infer_complete te, hM] at h
        rcases eb : eval n Γ ρ (if bc then th else el) with _ | _ | w <;>
          simp only [eb, reduceCtorEq, Option.some.injEq] at h
        have branchTyped : ValTyped w (if bc then A₁ else B₁) := by
          cases bc
          · exact eval_sound n te henv eb
          · exact eval_sound n tt henv eb
        exact castTo_typed branchTyped h
      | num _ => simp at h
      | clo _ _ _ _ _ _ => simp at h
    | @lam _ A₀ B₀ body tb =>
      simp only [eval, infer_complete tb, Option.some.injEq] at h
      subst h
      exact .clo henv tb (Prec.refl _) (Prec.refl _) (Prec.refl _)
    | @app _ f a F Aa D C tf ta hD _ hC =>
      simp only [eval] at h
      rcases ef : eval n Γ ρ f with _ | _ | vf <;> rcases ea : eval n Γ ρ a with _ | _ | va <;>
        simp only [ef, ea, reduceCtorEq, Option.some.injEq] at h
      cases vf with
      | clo cΓ cρ A body E₁ E₂ =>
        simp only at h
        have typedf := eval_sound n tf henv ef
        have typeda := eval_sound n ta henv ea
        cases typedf with
        | clo hcenv hbody h₁ h₂ harr =>
          rcases hcast : castTo va E₁ with _ | u <;>
            simp only [hcast, reduceCtorEq, Option.some.injEq] at h
          have typedu : ValTyped u A := (castTo_typed typeda hcast).mono h₁
          rcases eb : eval n (A :: cΓ) (u :: cρ) body with _ | _ | w <;>
            simp only [eb, reduceCtorEq, Option.some.injEq] at h
          have typedw := eval_sound n hbody (.cons typedu hcenv) eb
          exact (castTo_typed typedw h).mono (cod_bound harr hC)
      | num _ => simp at h
      | bool _ => simp at h
    | @asc _ s A₀ G ts _ =>
      simp only [eval] at h
      rcases es : eval n Γ ρ s with _ | _ | w <;> simp only [es, reduceCtorEq, Option.some.injEq] at h
      exact castTo_typed (eval_sound n ts henv es) h

/-! ## Annotation erasure -/

/-- **Erase every annotation to `?`.** -/
def erase : Term → Term
  | .var i => .var i
  | .num k => .num k
  | .bool b => .bool b
  | .add a b => .add (erase a) (erase b)
  | .ite c t e => .ite (erase c) (erase t) (erase e)
  | .lam _ body => .lam .unknown (erase body)
  | .app f a => .app (erase f) (erase a)
  | .asc t _ => .asc (erase t) .unknown

/-- Erasure is a precision step. -/
theorem termPrec_erase : ∀ t : Term, TermPrec t (erase t)
  | .var i => .var i
  | .num k => .num k
  | .bool b => .bool b
  | .add a b => .add (termPrec_erase a) (termPrec_erase b)
  | .ite c t e => .ite (termPrec_erase c) (termPrec_erase t) (termPrec_erase e)
  | .lam _ body => .lam (.unknown _) (termPrec_erase body)
  | .app f a => .app (termPrec_erase f) (termPrec_erase a)
  | .asc t _ => .asc (termPrec_erase t) (.unknown _)

/-- **Erasing annotations does not change a computed number.** -/
theorem erase_preserves_num {n : Nat} {t : Term} {k : Nat}
    (h : eval n [] [] t = some (some (.num k))) :
    eval n [] [] (erase t) = some (some (.num k)) := by
  obtain ⟨v', h', prec⟩ := dynamic_gradual_guarantee_value n ⟨.nil, .nil, termPrec_erase t⟩ h
  cases prec
  exact h'

/-- **Erasing annotations does not change a computed boolean.** -/
theorem erase_preserves_bool {n : Nat} {t : Term} {b : Bool}
    (h : eval n [] [] t = some (some (.bool b))) :
    eval n [] [] (erase t) = some (some (.bool b)) := by
  obtain ⟨v', h', prec⟩ := dynamic_gradual_guarantee_value n ⟨.nil, .nil, termPrec_erase t⟩ h
  cases prec
  exact h'

/-- **An annotated program computes what its erasure computes, or fails with
a run-time error.** -/
theorem annotated_agrees_or_fails {n : Nat} {t : Term} {k : Nat}
    (h : eval n [] [] (erase t) = some (some (.num k))) :
    eval n [] [] t = some none ∨ eval n [] [] t = some (some (.num k)) := by
  rcases dynamic_gradual_guarantee_error n ⟨.nil, .nil, termPrec_erase t⟩ h with
    failed | ⟨v, hv, prec⟩
  · exact Or.inl failed
  · cases prec
    exact Or.inr hv

/-! ## Controls -/

namespace Controls

/-- `(true :: ?) :: Int`. -/
def castTrueToInt : Term := .asc (.asc (.bool true) .unknown) .int

/-- `(true :: ?) :: ?`. -/
def castTrueToUnknown : Term := .asc (.asc (.bool true) .unknown) .unknown

/-- **A cast error**: `true` cannot pass as `Int`. -/
theorem cast_error : eval 3 [] [] castTrueToInt = some none := by
  rfl

/-- **The error case of the guarantee is inhabited**: the more precise program
fails where the less precise one succeeds. -/
theorem more_precise_fails :
    TermPrec castTrueToInt castTrueToUnknown ∧ eval 3 [] [] castTrueToInt = some none ∧
      ∃ v', eval 3 [] [] castTrueToUnknown = some (some v') :=
  ⟨.asc (.asc (.bool true) (Prec.refl _)) (.unknown _), cast_error, ⟨.bool true, rfl⟩⟩

/-- `((λx:Int. x) :: ?) true`: the argument is checked against the domain
evidence. -/
def domainMismatch : Term := .app (.asc (.lam .int (.var 0)) .unknown) (.bool true)

theorem domain_error : eval 4 [] [] domainMismatch = some none := by
  rfl

/-- `((λx:?. x) :: Bool → Int) true`: the result is checked against the
codomain evidence. -/
def codomainMismatch : Term :=
  .app (.asc (.lam .unknown (.var 0)) (.arr .bool .int)) (.bool true)

theorem codomain_error : eval 4 [] [] codomainMismatch = some none := by
  rfl

/-- `((λx:?. x) :: ?) true` runs. -/
def identityUnknown : Term := .app (.asc (.lam .unknown (.var 0)) .unknown) (.bool true)

theorem identity_runs : eval 4 [] [] identityUnknown = some (some (.bool true)) := by
  rfl

/-- `(λx:Int. x + 1) 2`. -/
def annotatedSuccessor : Term := .app (.lam .int (.add (.var 0) (.num 1))) (.num 2)

theorem annotatedSuccessor_runs : eval 5 [] [] annotatedSuccessor = some (some (.num 3)) := by
  rfl

/-- Its erasure computes the same number. -/
theorem erasedSuccessor_runs : eval 5 [] [] (erase annotatedSuccessor) = some (some (.num 3)) :=
  erase_preserves_num annotatedSuccessor_runs

/-- `(λx:Bool. x) 2`, with the annotation wrong: erased, it runs. -/
def wronglyAnnotated : Term := .app (.lam .bool (.var 0)) (.num 2)

/-- **A wrong annotation fails loudly**: the annotated program fails while its
erasure computes `2`. -/
theorem wrong_annotation_fails :
    eval 4 [] [] wronglyAnnotated = some none ∧
      eval 4 [] [] (erase wronglyAnnotated) = some (some (.num 2)) :=
  ⟨rfl, rfl⟩

end Controls

end Mettapedia.OSLF.Programs.DynamicGuarantee
