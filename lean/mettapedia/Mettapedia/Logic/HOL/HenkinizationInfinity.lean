import Mettapedia.Logic.HOL.HenkinizationStages
import Mettapedia.Logic.HOL.DerivationExtensionality

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/--
Canonical cumulative Henkin signature.

Base constants are normalized to a unique constructor, while witness and
counterexample constants remember the finite stage whose formula generated them.
-/
inductive HenkinConstInfinity (Base : Type u) (Const : Ty Base → Type v) :
    Ty Base → Type (max u (v + 1)) where
  | base : Const τ → HenkinConstInfinity Base Const τ
  | exWitness :
      {n : Nat} → {σ : Ty Base} →
        Formula (HenkinConstStage Base Const n) [σ] →
          HenkinConstInfinity Base Const σ
  | allCounterexample :
      {n : Nat} → {σ : Ty Base} →
        Formula (HenkinConstStage Base Const n) [σ] →
          HenkinConstInfinity Base Const σ

namespace HenkinConstInfinity

/-- Collapse any finite Henkin stage into the canonical cumulative signature. -/
def ofStage :
    {n : Nat} → {τ : Ty Base} →
      HenkinConstStage Base Const n τ →
        HenkinConstInfinity Base Const τ
  | 0, _, c => .base c.down
  | _ + 1, _, .base c => ofStage c
  | n + 1, _, .exWitness φ => .exWitness (n := n) φ
  | n + 1, _, .allCounterexample φ => .allCounterexample (n := n) φ

theorem ofStage_liftOffset :
    ∀ (k : Nat) {n : Nat} {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ),
      ofStage (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k c) =
        ofStage c
  | 0, _, _, c => by
      simp [HenkinConstStage.liftOffset]
  | k + 1, _, _, c => by
      change
        ofStage
            (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k c) =
          ofStage c
      exact ofStage_liftOffset k c

@[simp] theorem ofStage_ofBase {τ : Ty Base} (c : Const τ) :
    ofStage (HenkinConstStage.ofBase (Base := Base) c) = .base c := rfl

@[simp] theorem ofStage_cast
    {n m : Nat} (h : n = m) {τ : Ty Base}
    (c : HenkinConstStage Base Const n τ) :
    ofStage (Base := Base) (Const := Const)
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ) h) c) =
      ofStage (Base := Base) (Const := Const) c := by
  cases h
  rfl

theorem ofStage_eq_exWitness_stage_le
    {n : Nat} {σ : Ty Base}
    (c : HenkinConstStage Base Const n σ)
    {k : Nat} (φ : Formula (HenkinConstStage Base Const k) [σ])
    (h : ofStage (Base := Base) (Const := Const) c = .exWitness (n := k) φ) :
    k + 1 ≤ n := by
  induction n with
  | zero => cases c; cases h
  | succ n ih =>
      cases c with
      | base c =>
          change ofStage c = _ at h
          exact Nat.le_succ_of_le (ih c h)
      | exWitness φ' => injection h with hn _; omega
      | allCounterexample _ => cases h

theorem ofStage_eq_allCounterexample_stage_le
    {n : Nat} {σ : Ty Base}
    (c : HenkinConstStage Base Const n σ)
    {k : Nat} (φ : Formula (HenkinConstStage Base Const k) [σ])
    (h : ofStage (Base := Base) (Const := Const) c = .allCounterexample (n := k) φ) :
    k + 1 ≤ n := by
  induction n with
  | zero => cases c; cases h
  | succ n ih =>
      cases c with
      | base c =>
          change ofStage c = _ at h
          exact Nat.le_succ_of_le (ih c h)
      | exWitness _ => cases h
      | allCounterexample φ' => injection h with hn _; omega

theorem ofStage_ne_exWitness_future :
    ∀ {n m : Nat} (hnm : n ≤ m) {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ)
      (φ : Formula (HenkinConstStage Base Const m) [τ]),
      ofStage (Base := Base) (Const := Const) c ≠
        .exWitness (n := m) φ
  | 0, m, _, _, c, φ => by
      cases c
      intro h
      cases h
  | n + 1, m, hnm, _, c, φ => by
      cases c with
      | base c =>
          exact ofStage_ne_exWitness_future
            (Nat.le_trans (Nat.le_succ n) hnm) c φ
      | exWitness ψ =>
          intro h
          cases h
          exact Nat.not_succ_le_self n hnm
      | allCounterexample ψ =>
          intro h
          cases h

theorem ofStage_ne_allCounterexample_future :
    ∀ {n m : Nat} (hnm : n ≤ m) {τ : Ty Base}
      (c : HenkinConstStage Base Const n τ)
      (φ : Formula (HenkinConstStage Base Const m) [τ]),
      ofStage (Base := Base) (Const := Const) c ≠
        .allCounterexample (n := m) φ
  | 0, m, _, _, c, φ => by
      cases c
      intro h
      cases h
  | n + 1, m, hnm, _, c, φ => by
      cases c with
      | base c =>
          exact ofStage_ne_allCounterexample_future
            (Nat.le_trans (Nat.le_succ n) hnm) c φ
      | exWitness ψ =>
          intro h
          cases h
      | allCounterexample ψ =>
          intro h
          cases h
          exact Nat.not_succ_le_self n hnm

theorem ofStage_injective
    (n : Nat) {τ : Ty Base} :
    Function.Injective (@ofStage Base Const n τ) := by
  induction n with
  | zero =>
      intro c d h
      cases c
      cases d
      cases h
      rfl
  | succ n ih =>
      intro c d h
      cases c with
      | base c =>
          cases d with
          | base d =>
              have hcd : c = d := ih h
              cases hcd
              rfl
          | exWitness φ =>
              exfalso
              exact ofStage_ne_exWitness_future
                (n := n) (m := n)
                (Nat.le_refl n) c φ (by simpa using h)
          | allCounterexample φ =>
              exfalso
              exact ofStage_ne_allCounterexample_future
                (n := n) (m := n)
                (Nat.le_refl n) c φ (by simpa using h)
      | exWitness φ =>
          cases d with
          | base d =>
              exfalso
              exact ofStage_ne_exWitness_future
                (n := n) (m := n)
                (Nat.le_refl n) d φ (by simpa using h.symm)
          | exWitness ψ =>
              cases h
              rfl
          | allCounterexample ψ =>
              cases h
      | allCounterexample φ =>
          cases d with
          | base d =>
              exfalso
              exact ofStage_ne_allCounterexample_future
                (n := n) (m := n)
                (Nat.le_refl n) d φ (by simpa using h.symm)
          | exWitness ψ =>
              cases h
          | allCounterexample ψ =>
              cases h
              rfl

theorem ofStage_lift
    {m n : Nat} (hmn : m ≤ n) {τ : Ty Base}
    (c : HenkinConstStage Base Const m τ) :
    ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c) =
      ofStage (Base := Base) (Const := Const) c := by
  calc
    ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c) =
      ofStage (Base := Base) (Const := Const)
        (cast (congrArg (fun t => HenkinConstStage Base Const t τ)
            (Nat.add_sub_of_le hmn))
          (HenkinConstStage.liftOffset (Base := Base) (Const := Const) (n - m) c)) := by
            rw [HenkinConstStage.lift_eq_cast_liftOffset
              (Base := Base) (Const := Const) hmn c]
    _ =
      ofStage (Base := Base) (Const := Const)
        (HenkinConstStage.liftOffset (Base := Base) (Const := Const) (n - m) c) := by
          simpa using
            (ofStage_cast (Base := Base) (Const := Const)
              (h := Nat.add_sub_of_le hmn)
              (c := HenkinConstStage.liftOffset
                (Base := Base) (Const := Const) (n - m) c))
    _ = ofStage (Base := Base) (Const := Const) c := by
          simpa using
            (ofStage_liftOffset (Base := Base) (Const := Const)
              (k := n - m) (c := c))

/-- Directly lift an original-signature term into the cumulative Henkin signature. -/
abbrev liftBaseTerm {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → Term (HenkinConstInfinity Base Const) Γ τ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature formula into the cumulative Henkin signature. -/
abbrev liftBaseFormula {Γ : Ctx Base} :
    Formula Const Γ → Formula (HenkinConstInfinity Base Const) Γ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature closed term into the cumulative Henkin signature. -/
abbrev liftBaseClosedTerm {τ : Ty Base} :
    ClosedTerm Const τ → ClosedTerm (HenkinConstInfinity Base Const) τ :=
  mapConst HenkinConstInfinity.base

/-- Directly lift an original-signature closed formula into the cumulative Henkin signature. -/
abbrev liftBaseClosedFormula :
    ClosedFormula Const → ClosedFormula (HenkinConstInfinity Base Const) :=
  mapConst HenkinConstInfinity.base

/--
Recursive closed witness terms in the cumulative Henkin signature.

Positive example:
every simple type over `HenkinConstInfinity` is syntactically inhabited.

Negative example:
this does not say anything about the original source signature, whose base types
may still be syntactically empty.
-/
def witnessTerm : (τ : Ty Base) → ClosedTerm (HenkinConstInfinity Base Const) τ
  | .prop => .top
  | .base b =>
      .const (.exWitness
        (n := 0)
        (.top : Formula (HenkinConstStage Base Const 0) [.base b]))
  | .arr σ τ =>
      .lam (weaken
        (Base := Base)
        (Const := HenkinConstInfinity Base Const)
        (σ := σ)
        (witnessTerm τ))

@[simp] theorem witnessTerm_prop :
    witnessTerm (Base := Base) (Const := Const) .prop =
      (.top : ClosedFormula (HenkinConstInfinity Base Const)) :=
  rfl

@[simp] theorem witnessTerm_base (b : Base) :
    witnessTerm (Base := Base) (Const := Const) (.base b) =
      (.const (.exWitness
        (n := 0)
        (.top : Formula (HenkinConstStage Base Const 0) [.base b])) :
          ClosedTerm (HenkinConstInfinity Base Const) (.base b)) :=
  rfl

@[simp] theorem witnessTerm_arr (σ τ : Ty Base) :
    witnessTerm (Base := Base) (Const := Const) (σ ⇒ τ) =
      .lam (weaken
        (Base := Base)
        (Const := HenkinConstInfinity Base Const)
        (σ := σ)
        (witnessTerm (Base := Base) (Const := Const) τ)) :=
  rfl

/-- Every simple type in the cumulative Henkin signature has a closed witness term. -/
theorem nonempty_closedTerm (τ : Ty Base) :
    Nonempty (ClosedTerm (HenkinConstInfinity Base Const) τ) :=
  ⟨witnessTerm (Base := Base) (Const := Const) τ⟩

/--
The cumulative Henkin calculus proves `∃ x : τ, ⊤` at every simple type.

Positive example:
this is the syntactic inhabitance needed for default values in cumulative-Henkin
semantic constructions.

Negative example:
it does not imply that the original signature already had such witnesses.
-/
theorem theorem_existsTop (τ : Ty Base) :
    ExtDerivation.Theorem
      (HenkinConstInfinity Base Const)
      (.ex (.top : Formula (HenkinConstInfinity Base Const) [τ])) := by
  refine ExtDerivation.exI
    (witnessTerm (Base := Base) (Const := Const) τ) ?_
  simpa using
    (ExtDerivation.topI :
      ExtDerivation
        (HenkinConstInfinity Base Const)
        []
        (.top : ClosedFormula (HenkinConstInfinity Base Const)))

/-- Lift a finite-stage term into the canonical cumulative Henkin signature. -/
abbrev liftTerm {n : Nat} {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstInfinity Base Const) Γ τ :=
  mapConst (ofStage (Base := Base) (Const := Const))

/-- Lift a finite-stage formula into the canonical cumulative Henkin signature. -/
abbrev liftFormula {n : Nat} {Γ : Ctx Base} :
    Formula (HenkinConstStage Base Const n) Γ →
      Formula (HenkinConstInfinity Base Const) Γ :=
  mapConst (ofStage (Base := Base) (Const := Const))

/-- Lift a finite-stage closed formula into the canonical cumulative Henkin signature. -/
abbrev liftClosedFormula {n : Nat} :
    ClosedFormula (HenkinConstStage Base Const n) →
      ClosedFormula (HenkinConstInfinity Base Const) :=
  mapConst (ofStage (Base := Base) (Const := Const))

/-- If n ≤ k, the future exWitness constant at stage k does not occur
    in any term lifted from stage n. -/
theorem noConstOccurrence_liftTerm_exWitness_future
    {n k : Nat} (hnk : n ≤ k)
    {σ : Ty Base} (φ : Formula (HenkinConstStage Base Const k) [σ]) :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term (HenkinConstStage Base Const n) Γ τ),
      NoConstOccurrence (.exWitness (n := k) φ)
        (liftTerm (Base := Base) (Const := Const) t)
  | _, _, .var _ => .var
  | _, _, .const c => by
      by_cases hτ : σ = ‹_›
      · subst hτ; exact .const_same_ne _ (ofStage_ne_exWitness_future hnk c φ)
      · exact .const_diff_type hτ _
  | _, _, .app f t =>
      .app (noConstOccurrence_liftTerm_exWitness_future hnk φ f)
        (noConstOccurrence_liftTerm_exWitness_future hnk φ t)
  | _, _, .lam body =>
      .lam (noConstOccurrence_liftTerm_exWitness_future hnk φ body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q =>
      .and (noConstOccurrence_liftTerm_exWitness_future hnk φ p)
        (noConstOccurrence_liftTerm_exWitness_future hnk φ q)
  | _, _, .or p q =>
      .or (noConstOccurrence_liftTerm_exWitness_future hnk φ p)
        (noConstOccurrence_liftTerm_exWitness_future hnk φ q)
  | _, _, .imp p q =>
      .imp (noConstOccurrence_liftTerm_exWitness_future hnk φ p)
        (noConstOccurrence_liftTerm_exWitness_future hnk φ q)
  | _, _, .not p =>
      .not (noConstOccurrence_liftTerm_exWitness_future hnk φ p)
  | _, _, .eq t u =>
      .eq (noConstOccurrence_liftTerm_exWitness_future hnk φ t)
        (noConstOccurrence_liftTerm_exWitness_future hnk φ u)
  | _, _, .all p =>
      .all (noConstOccurrence_liftTerm_exWitness_future hnk φ p)
  | _, _, .ex p =>
      .ex (noConstOccurrence_liftTerm_exWitness_future hnk φ p)

/-- If n ≤ k, the future allCounterexample constant at stage k does not occur
    in any term lifted from stage n. -/
theorem noConstOccurrence_liftTerm_allCounterexample_future
    {n k : Nat} (hnk : n ≤ k)
    {σ : Ty Base} (φ : Formula (HenkinConstStage Base Const k) [σ]) :
    ∀ {Γ : Ctx Base} {τ : Ty Base}
      (t : Term (HenkinConstStage Base Const n) Γ τ),
      NoConstOccurrence (.allCounterexample (n := k) φ)
        (liftTerm (Base := Base) (Const := Const) t)
  | _, _, .var _ => .var
  | _, _, .const c => by
      by_cases hτ : σ = ‹_›
      · subst hτ; exact .const_same_ne _ (ofStage_ne_allCounterexample_future hnk c φ)
      · exact .const_diff_type hτ _
  | _, _, .app f t =>
      .app (noConstOccurrence_liftTerm_allCounterexample_future hnk φ f)
        (noConstOccurrence_liftTerm_allCounterexample_future hnk φ t)
  | _, _, .lam body =>
      .lam (noConstOccurrence_liftTerm_allCounterexample_future hnk φ body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q =>
      .and (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)
        (noConstOccurrence_liftTerm_allCounterexample_future hnk φ q)
  | _, _, .or p q =>
      .or (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)
        (noConstOccurrence_liftTerm_allCounterexample_future hnk φ q)
  | _, _, .imp p q =>
      .imp (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)
        (noConstOccurrence_liftTerm_allCounterexample_future hnk φ q)
  | _, _, .not p =>
      .not (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)
  | _, _, .eq t u =>
      .eq (noConstOccurrence_liftTerm_allCounterexample_future hnk φ t)
        (noConstOccurrence_liftTerm_allCounterexample_future hnk φ u)
  | _, _, .all p =>
      .all (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)
  | _, _, .ex p =>
      .ex (noConstOccurrence_liftTerm_allCounterexample_future hnk φ p)

@[simp] theorem liftBaseTerm_eq_liftTerm_zero
    {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    liftBaseTerm (Base := Base) (Const := Const) t =
      liftTerm (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) t) := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app g t hg ht => simp only [liftBaseTerm, liftTerm, mapConst, hg, ht]
  | lam t ih => simp only [liftBaseTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ => simp only [liftBaseTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu => simp only [liftBaseTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]
  | ex φ hφ => simp only [liftBaseTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftBaseFormula_eq_liftFormula_zero
    {Γ : Ctx Base} (φ : Formula Const Γ) :
    liftBaseFormula (Base := Base) (Const := Const) φ =
      liftFormula (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) φ) :=
  liftBaseTerm_eq_liftTerm_zero (Base := Base) (Const := Const) φ

@[simp] theorem liftBaseClosedFormula_eq_liftClosedFormula_zero
    (φ : ClosedFormula Const) :
    liftBaseClosedFormula (Base := Base) (Const := Const) φ =
      liftClosedFormula (Base := Base) (Const := Const)
        (mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) φ) :=
  liftBaseFormula_eq_liftFormula_zero (Base := Base) (Const := Const) φ

/-- Raise a finite-stage term by `k` additional Henkinization stages. -/
abbrev stageBumpTerm (k : Nat) {n : Nat} {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstStage Base Const (n + k)) Γ τ :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

/-- Raise a finite-stage formula by `k` additional Henkinization stages. -/
abbrev stageBumpFormula (k : Nat) {n : Nat} {Γ : Ctx Base} :
    Formula (HenkinConstStage Base Const n) Γ →
      Formula (HenkinConstStage Base Const (n + k)) Γ :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

/-- Raise a finite-stage closed formula by `k` additional Henkinization stages. -/
abbrev stageBumpClosedFormula (k : Nat) {n : Nat} :
    ClosedFormula (HenkinConstStage Base Const n) →
      ClosedFormula (HenkinConstStage Base Const (n + k)) :=
  mapConst (HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)

theorem liftTerm_stageBump (k : Nat) {n : Nat}
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const n) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (stageBumpTerm (Base := Base) (Const := Const) k t) =
      liftTerm (Base := Base) (Const := Const) t := by
  induction t with
  | var v => rfl
  | const c =>
      simp [stageBumpTerm, liftTerm, mapConst, ofStage_liftOffset]
  | app f t hf ht =>
      simp [stageBumpTerm, liftTerm, mapConst, hf, ht]
  | lam t ih =>
      simp [stageBumpTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu =>
      simp [stageBumpTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]
  | ex φ hφ =>
      simp [stageBumpTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftTerm_stageLift
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const m) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (HenkinConstStage.liftTerm (Base := Base) (Const := Const) hmn t) =
      liftTerm (Base := Base) (Const := Const) t := by
  induction t with
  | var v => rfl
  | const c =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ofStage_lift, hmn]
  | app g t hg ht =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hg, ht]
  | lam t ih =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ, hψ]
  | not φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]
  | eq t u ht hu =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, ht, hu]
  | all φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]
  | ex φ hφ =>
      simp [HenkinConstStage.liftTerm, liftTerm, mapConst, hφ]

@[simp] theorem liftFormula_stageLift
    {m n : Nat} (hmn : m ≤ n)
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const m) Γ) :
    liftFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn φ) =
      liftFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageLift (Base := Base) (Const := Const) hmn φ

@[simp] theorem liftClosedFormula_stageLift
    {m n : Nat} (hmn : m ≤ n)
    (φ : ClosedFormula (HenkinConstStage Base Const m)) :
    liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn φ) =
      liftClosedFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageLift (Base := Base) (Const := Const) hmn φ

@[simp] theorem liftFormula_weaken
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) Γ) :
    liftFormula (Base := Base) (Const := Const)
        (weaken (Base := Base) (Const := HenkinConstStage Base Const n) (σ := σ) φ) =
      weaken (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ)
        (liftFormula (Base := Base) (Const := Const) φ) := by
  simpa [liftFormula] using
    (Mettapedia.Logic.HOL.mapConst_weaken
      (Base := Base)
      (Const := HenkinConstStage Base Const n)
      (Const' := HenkinConstInfinity Base Const)
      (f := HenkinConstInfinity.ofStage (Base := Base) (Const := Const))
      (σ := σ)
      φ)

@[simp] theorem liftFormula_instantiate
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    (t : Term (HenkinConstStage Base Const n) Γ σ)
    (φ : Formula (HenkinConstStage Base Const n) (σ :: Γ)) :
    liftFormula (Base := Base) (Const := Const)
        (instantiate (Base := Base) t φ) =
      instantiate (Base := Base)
        (liftTerm (Base := Base) (Const := Const) t)
        (liftFormula (Base := Base) (Const := Const) φ) := by
  simpa [liftFormula, liftTerm] using
    (Mettapedia.Logic.HOL.mapConst_instantiate
      (Base := Base)
      (Const := HenkinConstStage Base Const n)
      (Const' := HenkinConstInfinity Base Const)
      (f := HenkinConstInfinity.ofStage (Base := Base) (Const := Const))
      t
      φ)


structure LiftFormulaListConsWitness
    {n : Nat} {Γ : Ctx Base}
    (Θ : List (Formula (HenkinConstStage Base Const n) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ)
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) where
  head : Formula (HenkinConstStage Base Const n) Γ
  tail : List (Formula (HenkinConstStage Base Const n) Γ)
  shape : Θ = head :: tail
  soundHead : liftFormula (Base := Base) (Const := Const) head = φ
  soundTail : tail.map (liftFormula (Base := Base) (Const := Const)) = Δ

def liftFormulaList_eq_cons_inv
    {n : Nat} {Γ : Ctx Base}
    {Θ : List (Formula (HenkinConstStage Base Const n) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    (h : Θ.map (liftFormula (Base := Base) (Const := Const)) = φ :: Δ) :
    LiftFormulaListConsWitness (Base := Base) (Const := Const) Θ φ Δ := by
  cases Θ with
  | nil =>
      simp at h
  | cons φ' Δ' =>
      simp at h
      exact ⟨φ', Δ', rfl, h.1, h.2⟩

@[simp] theorem liftBaseFormula_sound
    (n : Nat) {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    liftFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftBaseFormula (Base := Base) (Const := Const) n φ) =
      liftBaseFormula (Base := Base) (Const := Const) φ := by
  rw [HenkinConstStage.liftBaseFormula, liftFormula, liftBaseFormula,
    Mettapedia.Logic.HOL.mapConst_comp]
  apply Mettapedia.Logic.HOL.mapConst_ext
  intro τ c
  exact
    (ofStage_lift (Base := Base) (Const := Const)
      (Nat.zero_le n)
      (HenkinConstStage.ofBase (Base := Base) (Const := Const) c)).trans
      (ofStage_ofBase (Base := Base) (Const := Const) c)

@[simp] theorem liftBaseClosedFormula_sound
    (n : Nat)
    (φ : ClosedFormula Const) :
    liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ) =
      liftBaseClosedFormula (Base := Base) (Const := Const) φ :=
  liftBaseFormula_sound (Base := Base) (Const := Const) n φ

/-- Transport a finite-stage term across an equality of stage indices. -/
def castStageTerm {n m : Nat} (h : n = m) {Γ : Ctx Base} {τ : Ty Base} :
    Term (HenkinConstStage Base Const n) Γ τ →
      Term (HenkinConstStage Base Const m) Γ τ := by
  cases h
  intro t
  exact t

theorem liftTerm_castStageTerm {n m : Nat} (h : n = m)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstStage Base Const n) Γ τ) :
    liftTerm (Base := Base) (Const := Const)
        (castStageTerm (Base := Base) (Const := Const) h t) =
      liftTerm (Base := Base) (Const := Const) t := by
  cases h
  rfl

/-- A term over the cumulative signature together with a finite stage presentation. -/
structure StagedTerm {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ) where
  stage : Nat
  term : Term (HenkinConstStage Base Const stage) Γ τ
  sound : liftTerm (Base := Base) (Const := Const) term = t

/-- Recover a finite Henkin stage supporting a cumulative-signature term. -/
def stageTerm :
    {Γ : Ctx Base} → {τ : Ty Base} →
      (t : Term (HenkinConstInfinity Base Const) Γ τ) →
        StagedTerm (Base := Base) (Const := Const) t
  | _, _, .var v =>
      ⟨0, .var v, rfl⟩
  | _, _, .const (.base c) =>
      ⟨0, .const (HenkinConstStage.ofBase (Base := Base) c), rfl⟩
  | _, _, .const (.exWitness (n := n) φ) =>
      ⟨n + 1, .const (.exWitness φ), rfl⟩
  | _, _, .const (.allCounterexample (n := n) φ) =>
      ⟨n + 1, .const (.allCounterexample φ), rfl⟩
  | _, _, .app f t =>
      match stageTerm f, stageTerm t with
      | ⟨nf, tf, hf⟩, ⟨nt, tt, ht⟩ =>
          let tt' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nt nf)
              (stageBumpTerm (Base := Base) (Const := Const) nf tt)
          have hf' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nt tf) = f := by
            simpa [hf] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nt tf)
          have ht₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nf tt) = t := by
            simpa [ht] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nf tt)
          have ht' :
              liftTerm (Base := Base) (Const := Const) tt' = t := by
            unfold tt'
            rw [liftTerm_castStageTerm]
            exact ht₀
          ⟨nf + nt,
            .app
              (stageBumpTerm (Base := Base) (Const := Const) nt tf)
              tt',
            by
              cases hf'
              cases ht'
              rfl⟩
  | _, _, .lam t =>
      match stageTerm t with
      | ⟨n, t', ht⟩ =>
          ⟨n, .lam t', by
            cases ht
            rfl⟩
  | _, _, .top =>
      ⟨0, .top, rfl⟩
  | _, _, .bot =>
      ⟨0, .bot, rfl⟩
  | _, _, .and φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .and
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .or φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .or
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .imp φ ψ =>
      match stageTerm φ, stageTerm ψ with
      | ⟨nφ, tφ, hφ⟩, ⟨nψ, tψ, hψ⟩ =>
          let tψ' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nψ nφ)
              (stageBumpFormula (Base := Base) (Const := Const) nφ tψ)
          have hφ' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nψ tφ) = φ := by
            simpa [hφ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nψ tφ)
          have hψ₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpFormula (Base := Base) (Const := Const) nφ tψ) = ψ := by
            simpa [hψ] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nφ tψ)
          have hψ' :
              liftTerm (Base := Base) (Const := Const) tψ' = ψ := by
            unfold tψ'
            rw [liftTerm_castStageTerm]
            exact hψ₀
          ⟨nφ + nψ,
            .imp
              (stageBumpFormula (Base := Base) (Const := Const) nψ tφ)
              tψ',
            by
              cases hφ'
              cases hψ'
              rfl⟩
  | _, _, .not φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .not tφ, by
            cases hφ
            rfl⟩
  | _, _, .eq t u =>
      match stageTerm t, stageTerm u with
      | ⟨nt, tt, ht⟩, ⟨nu, tu, hu⟩ =>
          let tu' :=
            castStageTerm (Base := Base) (Const := Const)
              (Nat.add_comm nu nt)
              (stageBumpTerm (Base := Base) (Const := Const) nt tu)
          have ht' :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nu tt) = t := by
            simpa [ht] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nu tt)
          have hu₀ :
              liftTerm (Base := Base) (Const := Const)
                  (stageBumpTerm (Base := Base) (Const := Const) nt tu) = u := by
            simpa [hu] using
              (liftTerm_stageBump (Base := Base) (Const := Const) nt tu)
          have hu' :
              liftTerm (Base := Base) (Const := Const) tu' = u := by
            unfold tu'
            rw [liftTerm_castStageTerm]
            exact hu₀
          ⟨nt + nu,
            .eq
              (stageBumpTerm (Base := Base) (Const := Const) nu tt)
              tu',
            by
              cases ht'
              cases hu'
              rfl⟩
  | _, _, .all φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .all tφ, by
            cases hφ
            rfl⟩
  | _, _, .ex φ =>
      match stageTerm φ with
      | ⟨nφ, tφ, hφ⟩ =>
          ⟨nφ, .ex tφ, by
            cases hφ
            rfl⟩

theorem exists_stage_term {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ) :
    ∃ n, ∃ t' : Term (HenkinConstStage Base Const n) Γ τ,
      liftTerm (Base := Base) (Const := Const) t' = t := by
  let st := stageTerm (Base := Base) (Const := Const) t
  exact ⟨st.stage, st.term, st.sound⟩

theorem exists_stage_formula {Γ : Ctx Base}
    (φ : Formula (HenkinConstInfinity Base Const) Γ) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
      liftFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_term (Base := Base) (Const := Const) φ

/-- A finite-stage presentation of a cumulative-signature formula list. -/
structure StagedFormulaList {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) where
  stage : Nat
  formulas : List (Formula (HenkinConstStage Base Const stage) Γ)
  sound : formulas.map (liftFormula (Base := Base) (Const := Const)) = Δ

/-- Canonically stage a cumulative-signature formula list. -/
def stageFormulaList :
    {Γ : Ctx Base} →
      (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) →
        StagedFormulaList (Base := Base) (Const := Const) Δ
  | Γ, [] =>
      ⟨0, [], rfl⟩
  | Γ, φ :: Δ =>
      let sφ : StagedTerm (Base := Base) (Const := Const) φ :=
        stageTerm (Base := Base) (Const := Const) φ
      let sΔ : StagedFormulaList (Base := Base) (Const := Const) Δ :=
        stageFormulaList Δ
      let φ'' : Formula (HenkinConstStage Base Const (sφ.stage + sΔ.stage)) Γ :=
        stageBumpFormula (Base := Base) (Const := Const) sΔ.stage sφ.term
      let Δ'' : List (Formula (HenkinConstStage Base Const (sφ.stage + sΔ.stage)) Γ) :=
        sΔ.formulas.map (fun ψ =>
          castStageTerm (Base := Base) (Const := Const)
            (Nat.add_comm sΔ.stage sφ.stage)
            (stageBumpFormula (Base := Base) (Const := Const) sφ.stage ψ))
      have hφ'' :
          liftFormula (Base := Base) (Const := Const) φ'' = φ := by
        simpa [φ'', sφ.sound] using
          (liftTerm_stageBump (Base := Base) (Const := Const) sΔ.stage sφ.term)
      have hΔ'' :
          Δ''.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
        have hmaplift :
            ∀ Λ :
              List
                (Formula (HenkinConstStage Base Const sΔ.stage) Γ),
              Λ.map (fun ψ =>
                liftFormula (Base := Base) (Const := Const)
                  (castStageTerm (Base := Base) (Const := Const)
                    (Nat.add_comm sΔ.stage sφ.stage)
                    (stageBumpFormula (Base := Base) (Const := Const)
                      sφ.stage ψ))) =
                Λ.map (liftFormula (Base := Base) (Const := Const)) := by
          intro Λ
          induction Λ with
          | nil => rfl
          | cons ψ Λ ih =>
              simp only [List.map]
              rw [List.cons.injEq]
              refine ⟨?_, ih⟩
              calc
                liftFormula (Base := Base) (Const := Const)
                    (castStageTerm (Base := Base) (Const := Const)
                      (Nat.add_comm sΔ.stage sφ.stage)
                      (stageBumpFormula (Base := Base) (Const := Const)
                        sφ.stage ψ))
                    =
                  liftFormula (Base := Base) (Const := Const)
                    (stageBumpFormula (Base := Base) (Const := Const)
                      sφ.stage ψ) := by
                        simpa using
                          (liftTerm_castStageTerm (Base := Base) (Const := Const)
                            (Nat.add_comm sΔ.stage sφ.stage)
                            (stageBumpFormula (Base := Base) (Const := Const)
                              sφ.stage ψ))
                _ =
                  liftFormula (Base := Base) (Const := Const) ψ := by
                    simpa using
                      (liftTerm_stageBump (Base := Base) (Const := Const)
                        sφ.stage ψ)
        calc
          Δ''.map (liftFormula (Base := Base) (Const := Const))
              = sΔ.formulas.map (fun ψ =>
                  liftFormula (Base := Base) (Const := Const)
                    (castStageTerm (Base := Base) (Const := Const)
                      (Nat.add_comm sΔ.stage sφ.stage)
                      (stageBumpFormula (Base := Base) (Const := Const)
                        sφ.stage ψ))) := by
                  simp [Δ'']
          _ = sΔ.formulas.map (liftFormula (Base := Base) (Const := Const)) :=
                hmaplift sΔ.formulas
          _ = Δ := sΔ.sound
      ⟨sφ.stage + sΔ.stage, φ'' :: Δ'', by
        simp [hφ'', hΔ'']⟩

theorem exists_stage_formulaList {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) :
    ∃ n, ∃ Δ' : List (Formula (HenkinConstStage Base Const n) Γ),
      Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
  let sΔ := stageFormulaList (Base := Base) (Const := Const) Δ
  exact ⟨sΔ.stage, sΔ.formulas, sΔ.sound⟩

theorem exists_stage_closedFormula
    (φ : ClosedFormula (HenkinConstInfinity Base Const)) :
    ∃ n, ∃ φ' : ClosedFormula (HenkinConstStage Base Const n),
      liftClosedFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_formula (Base := Base) (Const := Const) φ

theorem exists_stage_closedTheory
    (Δ : List (ClosedFormula (HenkinConstInfinity Base Const))) :
    ∃ n, ∃ Δ' : List (ClosedFormula (HenkinConstStage Base Const n)),
      Δ'.map (liftClosedFormula (Base := Base) (Const := Const)) = Δ :=
  exists_stage_formulaList (Base := Base) (Const := Const) Δ

def stageTermTo {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ)
    {n : Nat}
    (h : (stageTerm (Base := Base) (Const := Const) t).stage ≤ n) :
    Term (HenkinConstStage Base Const n) Γ τ :=
  HenkinConstStage.liftTerm (Base := Base) (Const := Const) h
    (stageTerm (Base := Base) (Const := Const) t).term

@[simp] theorem stageTermTo_sound {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ)
    {n : Nat}
    (h : (stageTerm (Base := Base) (Const := Const) t).stage ≤ n) :
    liftTerm (Base := Base) (Const := Const)
        (stageTermTo (Base := Base) (Const := Const) t h) = t := by
  let st := stageTerm (Base := Base) (Const := Const) t
  change
    liftTerm (Base := Base) (Const := Const)
        (HenkinConstStage.liftTerm (Base := Base) (Const := Const) h st.term) = t
  exact (liftTerm_stageLift (Base := Base) (Const := Const) h st.term).trans st.sound

def stageFormulaTo {Γ : Ctx Base}
    (φ : Formula (HenkinConstInfinity Base Const) Γ)
    {n : Nat}
    (h : (stageTerm (Base := Base) (Const := Const) φ).stage ≤ n) :
    Formula (HenkinConstStage Base Const n) Γ :=
  stageTermTo (Base := Base) (Const := Const) φ h

@[simp] theorem stageFormulaTo_sound {Γ : Ctx Base}
    (φ : Formula (HenkinConstInfinity Base Const) Γ)
    {n : Nat}
    (h : (stageTerm (Base := Base) (Const := Const) φ).stage ≤ n) :
    liftFormula (Base := Base) (Const := Const)
        (stageFormulaTo (Base := Base) (Const := Const) φ h) = φ :=
  stageTermTo_sound (Base := Base) (Const := Const) φ h

@[simp] theorem liftFormula_stageBump (k : Nat) {n : Nat}
    {Γ : Ctx Base}
    (φ : Formula (HenkinConstStage Base Const n) Γ) :
    liftFormula (Base := Base) (Const := Const)
        (stageBumpFormula (Base := Base) (Const := Const) k φ) =
      liftFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageBump (Base := Base) (Const := Const) k φ

@[simp] theorem liftClosedFormula_stageBump (k : Nat) {n : Nat}
    (φ : ClosedFormula (HenkinConstStage Base Const n)) :
    liftClosedFormula (Base := Base) (Const := Const)
        (stageBumpClosedFormula (Base := Base) (Const := Const) k φ) =
      liftClosedFormula (Base := Base) (Const := Const) φ :=
  liftTerm_stageBump (Base := Base) (Const := Const) k φ

theorem liftTerm_injective {n : Nat}
    {Γ : Ctx Base} {τ : Ty Base} :
    Function.Injective
      (@liftTerm Base Const n Γ τ) := by
  intro t u h
  induction t with
  | var v =>
      cases u <;> cases h <;> rfl
  | const c =>
      cases u with
      | const d =>
          have hcd :
              ofStage (Base := Base) (Const := Const) c =
                ofStage (Base := Base) (Const := Const) d := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hc : c = d :=
            ofStage_injective (Base := Base) (Const := Const) n hcd
          cases hc
          rfl
      | _ =>
          cases h
  | app g t hg ht =>
      cases u with
      | app g' t' =>
          injection h with hΓ hσ hτ hg' ht'
          cases hΓ
          cases hσ
          cases hτ
          have hgEq : g = g' := hg (by simpa [liftTerm] using hg')
          have htEq : t = t' := ht (by simpa [liftTerm] using ht')
          cases hgEq
          cases htEq
          rfl
      | _ =>
          cases h
  | lam t ih =>
      cases u with
      | lam u =>
          have htu :
              liftTerm (Base := Base) (Const := Const) t =
                liftTerm (Base := Base) (Const := Const) u := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hEq : t = u := ih htu
          cases hEq
          rfl
      | _ =>
          cases h
  | top =>
      cases u <;> cases h <;> rfl
  | bot =>
      cases u <;> cases h <;> rfl
  | and φ ψ hφ hψ =>
      cases u with
      | and φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | or φ ψ hφ hψ =>
      cases u with
      | or φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | imp φ ψ hφ hψ =>
      cases u with
      | imp φ' ψ' =>
          have hpair :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) φ' ∧
              liftTerm (Base := Base) (Const := Const) ψ =
                liftTerm (Base := Base) (Const := Const) ψ' := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          rcases hpair with ⟨hφ', hψ'⟩
          have hφEq : φ = φ' := hφ hφ'
          have hψEq : ψ = ψ' := hψ hψ'
          cases hφEq
          cases hψEq
          rfl
      | _ =>
          cases h
  | not φ hφ =>
      cases u with
      | not ψ =>
          have hφ' :
              liftTerm (Base := Base) (Const := Const) φ =
                liftTerm (Base := Base) (Const := Const) ψ := by
            simpa [liftTerm, Mettapedia.Logic.HOL.mapConst] using h
          have hEq : φ = ψ := hφ hφ'
          cases hEq
          rfl
      | _ =>
          cases h
  | eq t u ht hu =>
      cases u with
      | eq t' u' =>
          injection h with hΓ hτ ht' hu'
          cases hΓ
          cases hτ
          have htEq : t = t' := ht (by simpa [liftTerm] using ht')
          have huEq : u = u' := hu (by simpa [liftTerm] using hu')
          cases htEq
          cases huEq
          rfl
      | _ =>
          cases h
  | all φ hφ =>
      cases u with
      | all ψ =>
          injection h with hΓ hσ hφ'
          cases hΓ
          cases hσ
          have hEq : φ = ψ := hφ (by simpa [liftTerm] using hφ')
          cases hEq
          rfl
      | _ =>
          cases h
  | ex φ hφ =>
      cases u with
      | ex ψ =>
          injection h with hΓ hσ hφ'
          cases hΓ
          cases hσ
          have hEq : φ = ψ := hφ (by simpa [liftTerm] using hφ')
          cases hEq
          rfl
      | _ =>
          cases h

theorem liftFormula_injective {n : Nat}
    {Γ : Ctx Base} :
    Function.Injective
      (@liftFormula Base Const n Γ) :=
  liftTerm_injective (Base := Base) (Const := Const) (n := n)

theorem liftClosedFormula_injective {n : Nat} :
    Function.Injective
      (@liftClosedFormula Base Const n) :=
  liftFormula_injective (Base := Base) (Const := Const) (n := n)

theorem liftFormulaList_injective {n : Nat}
    {Γ : Ctx Base} :
    Function.Injective
      (fun Δ : List (Formula (HenkinConstStage Base Const n) Γ) =>
        Δ.map (liftFormula (Base := Base) (Const := Const))) := by
  intro Δ Ξ h
  induction Δ generalizing Ξ with
  | nil =>
      cases Ξ with
      | nil => rfl
      | cons ψ Ξ => cases h
  | cons φ Δ ih =>
      cases Ξ with
      | nil => cases h
      | cons ψ Ξ =>
          injection h with hφ hΔ
          have hφEq : φ = ψ :=
            liftFormula_injective (Base := Base) (Const := Const) (n := n) hφ
          have hΔEq : Δ = Ξ := ih hΔ
          cases hφEq
          cases hΔEq
          rfl

/-- A finite-stage presentation of a cumulative-signature judgement. -/
structure StagedJudgement {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) where
  stage : Nat
  context : List (Formula (HenkinConstStage Base Const stage) Γ)
  formula : Formula (HenkinConstStage Base Const stage) Γ
  soundContext : context.map (liftFormula (Base := Base) (Const := Const)) = Δ
  soundFormula : liftFormula (Base := Base) (Const := Const) formula = φ

/-- Canonically stage a cumulative-signature judgement. -/
def stageJudgement :
    {Γ : Ctx Base} →
      (Δ : List (Formula (HenkinConstInfinity Base Const) Γ)) →
      (φ : Formula (HenkinConstInfinity Base Const) Γ) →
        StagedJudgement (Base := Base) (Const := Const) Δ φ
  | Γ, Δ, φ =>
      match stageFormulaList (φ :: Δ) with
      | ⟨n, [], hΘ⟩ =>
          False.elim (by simp at hΘ)
      | ⟨n, φ' :: Δ', hΘ⟩ =>
          have hsplit :
              liftFormula (Base := Base) (Const := Const) φ' = φ ∧
                Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := by
            simpa using hΘ
          ⟨n, Δ', φ', hsplit.2, hsplit.1⟩

/--
A finite-stage presentation of a cumulative-signature derivation.

This is the generic derivation-carrying staging object the council wants as the
real induction engine: unlike the original-lift-specific wrappers downstream,
it works for arbitrary variable contexts and arbitrary cumulative judgements.
-/
structure SupportedStageDerivation {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) where
  stage : Nat
  context : List (Formula (HenkinConstStage Base Const stage) Γ)
  formula : Formula (HenkinConstStage Base Const stage) Γ
  soundContext : context.map (liftFormula (Base := Base) (Const := Const)) = Δ
  soundFormula : liftFormula (Base := Base) (Const := Const) formula = φ
  deriv : ExtDerivation (HenkinConstStage Base Const stage) context formula

def SupportedStageDerivation.decomposeConsContext
    {Γ : Ctx Base}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) (φ :: Δ) ψ) :
    LiftFormulaListConsWitness
      (Base := Base)
      (Const := Const)
      S.context
      φ
      Δ :=
  liftFormulaList_eq_cons_inv
    (Base := Base) (Const := Const) (Θ := S.context) (h := S.soundContext)

def SupportedStageDerivation.weakenVar
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    {σ : Ty Base}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    SupportedStageDerivation
      (Base := Base)
      (Const := Const)
      (weakenHyps (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) Δ)
      (weaken (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) φ) := by
  refine
    { stage := S.stage
      context :=
        weakenHyps
          (Base := Base)
          (Const := HenkinConstStage Base Const S.stage)
          (σ := σ)
          S.context
      formula := weaken (Base := Base) (Const := HenkinConstStage Base Const S.stage) (σ := σ) S.formula
      soundContext := ?_
      soundFormula := ?_
      deriv := ?_ }
  · calc
      List.map (liftFormula (Base := Base) (Const := Const))
          (weakenHyps
            (Base := Base)
            (Const := HenkinConstStage Base Const S.stage)
            (σ := σ)
            S.context) =
        List.map
          (weaken (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ))
          (List.map (liftFormula (Base := Base) (Const := Const)) S.context) := by
            simp [weakenHyps, List.map_map, Function.comp, liftFormula_weaken]
      _ =
        weakenHyps
          (Base := Base)
          (Const := HenkinConstInfinity Base Const)
          (σ := σ)
          Δ := by
            simpa [weakenHyps] using congrArg
              (List.map
                (weaken (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ)))
              S.soundContext
  · simpa [liftFormula_weaken, S.soundFormula]
  · simpa [weakenHyps] using
      (ExtDerivation.rename
        (Base := Base)
        (Const := HenkinConstStage Base Const S.stage)
        (Γ := Γ)
        (Δ := S.context)
        (φ := S.formula)
        (Γ' := σ :: Γ)
        (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
        S.deriv)

def SupportedStageDerivation.prependAssumption
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ)
    (φ' : Formula (HenkinConstStage Base Const S.stage) Γ)
    (hφ' : liftFormula (Base := Base) (Const := Const) φ' = φ) :
    SupportedStageDerivation (Base := Base) (Const := Const) (φ :: Δ) ψ := by
  refine
    { stage := S.stage
      context := φ' :: S.context
      formula := S.formula
      soundContext := ?_
      soundFormula := S.soundFormula
      deriv := ?_ }
  · simp [hφ', S.soundContext]
  · exact
      ExtDerivation.mono
        (Base := Base)
        (Const := HenkinConstStage Base Const S.stage)
        (Δ := S.context)
        (Δ' := φ' :: S.context)
        (φ := S.formula)
        (by
          intro χ hχ
          simp [hχ])
        S.deriv

def SupportedStageDerivation.toStagedJudgement
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    StagedJudgement (Base := Base) (Const := Const) Δ φ where
  stage := S.stage
  context := S.context
  formula := S.formula
  soundContext := S.soundContext
  soundFormula := S.soundFormula

def SupportedStageDerivation.castStage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    {n : Nat} (h : S.stage = n) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  cases h
  exact S

/--
Raise a supported staged derivation by `k` additional finite Henkin stages.

This is the generic stage-alignment operation needed later when multiple
subderivations have to be brought to a common finite stage.
-/
def SupportedStageDerivation.bump
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    (k : Nat) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  refine
    { stage := S.stage + k
      context := S.context.map (stageBumpFormula (Base := Base) (Const := Const) k)
      formula := stageBumpFormula (Base := Base) (Const := Const) k S.formula
      soundContext := ?_
      soundFormula := ?_
      deriv := ?_ }
  · calc
      List.map (liftFormula (Base := Base) (Const := Const))
          (List.map (stageBumpFormula (Base := Base) (Const := Const) k) S.context) =
        List.map
          (fun ψ =>
            liftFormula (Base := Base) (Const := Const)
              (stageBumpFormula (Base := Base) (Const := Const) k ψ))
          S.context := by
            simp [List.map_map]
      _ =
        List.map
          (fun ψ => liftFormula (Base := Base) (Const := Const) ψ)
          S.context := by
            have hpoint :
                ∀ ψ : Formula (HenkinConstStage Base Const S.stage) Γ,
                  liftFormula (Base := Base) (Const := Const)
                      (stageBumpFormula (Base := Base) (Const := Const) k ψ) =
                    liftFormula (Base := Base) (Const := Const) ψ := by
              intro ψ
              exact liftFormula_stageBump (Base := Base) (Const := Const) k ψ
            induction S.context with
            | nil => rfl
            | cons ψ Γ ih =>
                simp only [List.map, hpoint ψ, ih]
      _ = Δ := S.soundContext
  · exact (liftFormula_stageBump (Base := Base) (Const := Const) k S.formula).trans S.soundFormula
  · simpa [stageBumpFormula, Mettapedia.Logic.HOL.mapConst] using
      (ExtDerivation.mapConst
        (Base := Base)
        (Const := HenkinConstStage Base Const S.stage)
        (Const' := HenkinConstStage Base Const (S.stage + k))
        (f := HenkinConstStage.liftOffset (Base := Base) (Const := Const) k)
        (Δ := S.context)
        (φ := S.formula)
        S.deriv)

theorem stagedFormulaList_preimage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    (S : StagedFormulaList (Base := Base) (Const := Const) Δ)
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ) :
    ∃ φ' : Formula (HenkinConstStage Base Const S.stage) Γ,
      φ' ∈ S.formulas ∧
        liftFormula (Base := Base) (Const := Const) φ' = φ := by
  have hφ' : φ ∈ S.formulas.map (liftFormula (Base := Base) (Const := Const)) := by
    simpa [S.sound] using hφ
  rcases List.mem_map.mp hφ' with ⟨φ', hφ'mem, hEq⟩
  exact ⟨φ', hφ'mem, hEq⟩

theorem stageJudgement_context_preimage
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (hψ : ψ ∈ Δ) :
    ∃ ψ' :
        Formula
          (HenkinConstStage Base Const
            (stageJudgement (Base := Base) (Const := Const) Δ ψ).stage) Γ,
      ψ' ∈ (stageJudgement (Base := Base) (Const := Const) Δ ψ).context ∧
        liftFormula (Base := Base) (Const := Const) ψ' = ψ := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ ψ
  exact stagedFormulaList_preimage
    (Base := Base) (Const := Const)
    ⟨S.stage, S.context, S.soundContext⟩ hψ

theorem supportedStageDerivation_hyp
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ) :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ φ
  rcases stageJudgement_context_preimage
      (Base := Base) (Const := Const) (Δ := Δ) (ψ := φ) hφ with
    ⟨φ', hφ', hlift⟩
  have hEq : φ' = S.formula :=
    liftFormula_injective (Base := Base) (Const := Const) (n := S.stage)
      (hlift.trans S.soundFormula.symm)
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        subst hEq
        exact ExtDerivation.hyp hφ' }⟩

theorem supportedStageDerivation_topI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)} :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ (.top : Formula _ Γ)) := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ (.top : Formula _ Γ)
  have hEq : S.formula = (.top : Formula (HenkinConstStage Base Const S.stage) Γ) :=
    liftFormula_injective (Base := Base) (Const := Const) (n := S.stage)
      (S.soundFormula.trans rfl.symm)
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        simpa [hEq] using
          (ExtDerivation.topI :
            ExtDerivation (HenkinConstStage Base Const S.stage) S.context
              (.top : Formula (HenkinConstStage Base Const S.stage) Γ)) }⟩

-- Term-level lift witnesses for nested inversion (beta, eta)

structure AppLiftWitness
    {n : Nat} {Γ : Ctx Base} {σ τ : Ty Base}
    (θ : Term (HenkinConstStage Base Const n) Γ τ)
    (f : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ))
    (t : Term (HenkinConstInfinity Base Const) Γ σ) where
  fn : Term (HenkinConstStage Base Const n) Γ (σ ⇒ τ)
  arg : Term (HenkinConstStage Base Const n) Γ σ
  shape : θ = .app fn arg
  soundFn : liftTerm (Base := Base) (Const := Const) fn = f
  soundArg : liftTerm (Base := Base) (Const := Const) arg = t

def liftTerm_eq_app_inv
    {n : Nat} {Γ : Ctx Base} {σ τ : Ty Base}
    {θ : Term (HenkinConstStage Base Const n) Γ τ}
    {f : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ)}
    {t : Term (HenkinConstInfinity Base Const) Γ σ}
    (h : liftTerm (Base := Base) (Const := Const) θ = .app f t) :
    AppLiftWitness (Base := Base) (Const := Const) θ f t := by
  cases θ with
  | app fn arg =>
      injection h with _ hσ _ hfn harg
      subst hσ
      exact ⟨fn, arg, rfl, eq_of_heq hfn, eq_of_heq harg⟩
  | _ => simp [liftTerm, mapConst] at h

structure LamLiftWitness
    {n : Nat} {Γ : Ctx Base} {σ τ : Ty Base}
    (θ : Term (HenkinConstStage Base Const n) Γ (σ ⇒ τ))
    (body : Term (HenkinConstInfinity Base Const) (σ :: Γ) τ) where
  stageBody : Term (HenkinConstStage Base Const n) (σ :: Γ) τ
  shape : θ = .lam stageBody
  soundBody : liftTerm (Base := Base) (Const := Const) stageBody = body

def liftTerm_eq_lam_inv
    {n : Nat} {Γ : Ctx Base} {σ τ : Ty Base}
    {θ : Term (HenkinConstStage Base Const n) Γ (σ ⇒ τ)}
    {body : Term (HenkinConstInfinity Base Const) (σ :: Γ) τ}
    (h : liftTerm (Base := Base) (Const := Const) θ = .lam body) :
    LamLiftWitness (Base := Base) (Const := Const) θ body := by
  cases θ with
  | lam t =>
      simp [liftTerm, mapConst] at h
      exact ⟨t, rfl, h⟩
  | _ => simp [liftTerm, mapConst] at h

-- Formula-level lift witnesses

structure AndLiftWitness
    {n : Nat} {Γ : Ctx Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ ψ : Formula (HenkinConstInfinity Base Const) Γ) where
  left : Formula (HenkinConstStage Base Const n) Γ
  right : Formula (HenkinConstStage Base Const n) Γ
  shape : θ = .and left right
  soundLeft :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) left = φ
  soundRight :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) right = ψ

structure OrLiftWitness
    {n : Nat} {Γ : Ctx Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ ψ : Formula (HenkinConstInfinity Base Const) Γ) where
  left : Formula (HenkinConstStage Base Const n) Γ
  right : Formula (HenkinConstStage Base Const n) Γ
  shape : θ = .or left right
  soundLeft :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) left = φ
  soundRight :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) right = ψ

structure ImpLiftWitness
    {n : Nat} {Γ : Ctx Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ ψ : Formula (HenkinConstInfinity Base Const) Γ) where
  antecedent : Formula (HenkinConstStage Base Const n) Γ
  consequent : Formula (HenkinConstStage Base Const n) Γ
  shape : θ = .imp antecedent consequent
  soundAntecedent :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) antecedent = φ
  soundConsequent :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) consequent = ψ

structure NotLiftWitness
    {n : Nat} {Γ : Ctx Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ : Formula (HenkinConstInfinity Base Const) Γ) where
  body : Formula (HenkinConstStage Base Const n) Γ
  shape : θ = .not body
  soundBody :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) body = φ

structure AllLiftWitness
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)) where
  body : Formula (HenkinConstStage Base Const n) (σ :: Γ)
  shape : θ = .all body
  soundBody :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) body = φ

structure ExLiftWitness
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)) where
  body : Formula (HenkinConstStage Base Const n) (σ :: Γ)
  shape : θ = .ex body
  soundBody :
    HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) body = φ

structure EqLiftWitness
    {n : Nat} {Γ : Ctx Base} {τ : Ty Base}
    (θ : Formula (HenkinConstStage Base Const n) Γ)
    (t u : Term (HenkinConstInfinity Base Const) Γ τ) where
  left : Term (HenkinConstStage Base Const n) Γ τ
  right : Term (HenkinConstStage Base Const n) Γ τ
  shape : θ = .eq left right
  soundLeft :
    HenkinConstInfinity.liftTerm (Base := Base) (Const := Const) left = t
  soundRight :
    HenkinConstInfinity.liftTerm (Base := Base) (Const := Const) right = u

def liftFormula_eq_eq_inv
    {n : Nat} {Γ : Ctx Base} {τ : Ty Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {t u : Term (HenkinConstInfinity Base Const) Γ τ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .eq t u) :
    EqLiftWitness (Base := Base) (Const := Const) θ t u := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t' => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t' u' =>
      injection h with _ hτ ht' hu'
      subst hτ
      exact ⟨t', u', rfl, eq_of_heq ht', eq_of_heq hu'⟩
  | all φ' => cases h
  | ex φ' => cases h

def liftFormula_eq_and_inv
    {n : Nat} {Γ : Ctx Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .and φ ψ) :
    AndLiftWitness (Base := Base) (Const := Const) θ φ ψ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' =>
      simp [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst] at h
      exact ⟨φ', ψ', rfl, h.1, h.2⟩
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' => cases h

def liftFormula_eq_or_inv
    {n : Nat} {Γ : Ctx Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .or φ ψ) :
    OrLiftWitness (Base := Base) (Const := Const) θ φ ψ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' =>
      simp [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst] at h
      exact ⟨φ', ψ', rfl, h.1, h.2⟩
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' => cases h

def liftFormula_eq_imp_inv
    {n : Nat} {Γ : Ctx Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .imp φ ψ) :
    ImpLiftWitness (Base := Base) (Const := Const) θ φ ψ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' => cases h
  | imp φ' ψ' =>
      simp [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst] at h
      exact ⟨φ', ψ', rfl, h.1, h.2⟩
  | not φ' => cases h
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' => cases h

def liftFormula_eq_not_inv
    {n : Nat} {Γ : Ctx Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .not φ) :
    NotLiftWitness (Base := Base) (Const := Const) θ φ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' =>
      simp [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst] at h
      exact ⟨φ', rfl, h⟩
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' => cases h

def liftFormula_eq_all_inv
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .all φ) :
    AllLiftWitness (Base := Base) (Const := Const) (σ := σ) θ φ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t u => cases h
  | all φ' =>
      cases h
      exact ⟨φ', rfl, rfl⟩
  | ex φ' => cases h

def liftFormula_eq_ex_inv
    {n : Nat} {Γ : Ctx Base} {σ : Ty Base}
    {θ : Formula (HenkinConstStage Base Const n) Γ}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    (h : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) θ = .ex φ) :
    ExLiftWitness (Base := Base) (Const := Const) (σ := σ) θ φ := by
  cases θ with
  | var v => cases h
  | const c => cases h
  | app f t => cases h
  | top => cases h
  | bot => cases h
  | and φ' ψ' => cases h
  | or φ' ψ' => cases h
  | imp φ' ψ' => cases h
  | not φ' => cases h
  | eq t u => cases h
  | all φ' => cases h
  | ex φ' =>
      cases h
      exact ⟨φ', rfl, rfl⟩


def SupportedStageDerivation.andEL
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.and φ ψ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  let shp :=
    liftFormula_eq_and_inv (Base := Base) (Const := Const) S.soundFormula
  let φ' := shp.left
  let ψ' := shp.right
  have hshape : S.formula = .and φ' ψ' := shp.shape
  have hφ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) φ' = φ :=
    shp.soundLeft
  refine
    { stage := S.stage
      context := S.context
      formula := φ'
      soundContext := S.soundContext
      soundFormula := hφ
      deriv := ?_ }
  have hderiv :
      ExtDerivation (HenkinConstStage Base Const S.stage) S.context (.and φ' ψ') := by
    simpa [hshape] using S.deriv
  exact ExtDerivation.andEL hderiv

def SupportedStageDerivation.andER
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.and φ ψ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ := by
  let shp :=
    liftFormula_eq_and_inv (Base := Base) (Const := Const) S.soundFormula
  let φ' := shp.left
  let ψ' := shp.right
  have hshape : S.formula = .and φ' ψ' := shp.shape
  have hψ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) ψ' = ψ :=
    shp.soundRight
  refine
    { stage := S.stage
      context := S.context
      formula := ψ'
      soundContext := S.soundContext
      soundFormula := hψ
      deriv := ?_ }
  have hderiv :
      ExtDerivation (HenkinConstStage Base Const S.stage) S.context (.and φ' ψ') := by
    simpa [hshape] using S.deriv
  exact ExtDerivation.andER hderiv

theorem exists_stage_judgement {Γ : Ctx Base}
    (Δ : List (Formula (HenkinConstInfinity Base Const) Γ))
    (φ : Formula (HenkinConstInfinity Base Const) Γ) :
    ∃ n, ∃ Δ' : List (Formula (HenkinConstStage Base Const n) Γ),
      ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
        Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ ∧
        liftFormula (Base := Base) (Const := Const) φ' = φ := by
  let sJ := stageJudgement (Base := Base) (Const := Const) Δ φ
  exact ⟨sJ.stage, sJ.context, sJ.formula, sJ.soundContext, sJ.soundFormula⟩

theorem exists_stage_closedJudgement
    (Δ : List (ClosedFormula (HenkinConstInfinity Base Const)))
    (φ : ClosedFormula (HenkinConstInfinity Base Const)) :
    ∃ n, ∃ Δ' : List (ClosedFormula (HenkinConstStage Base Const n)),
      ∃ φ' : ClosedFormula (HenkinConstStage Base Const n),
        Δ'.map (liftClosedFormula (Base := Base) (Const := Const)) = Δ ∧
        liftClosedFormula (Base := Base) (Const := Const) φ' = φ :=
  exists_stage_judgement (Base := Base) (Const := Const) Δ φ

theorem mem_liftFormula_preimage
    {Γ : Ctx Base} {n : Nat}
    {Δ : List (Formula (HenkinConstStage Base Const n) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (hφ : φ ∈ Δ.map (liftFormula (Base := Base) (Const := Const))) :
    ∃ φ' : Formula (HenkinConstStage Base Const n) Γ,
      φ' ∈ Δ ∧ liftFormula (Base := Base) (Const := Const) φ' = φ := by
  rcases List.mem_map.mp hφ with ⟨φ', hφ', hEq⟩
  exact ⟨φ', hφ', hEq⟩

theorem stageLift_formulaProvable
    {Γ : Ctx Base} {m n : Nat} (h : m ≤ n)
    {Δ : List (Formula (HenkinConstStage Base Const m) Γ)}
    {φ : Formula (HenkinConstStage Base Const m) Γ}
    (d : ExtDerivation (HenkinConstStage Base Const m) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h))
      (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h φ) := by
  simpa [HenkinConstStage.liftFormula, Mettapedia.Logic.HOL.mapConst] using
    (ExtDerivation.mapConst
      (Base := Base)
      (Const := HenkinConstStage Base Const m)
      (Const' := HenkinConstStage Base Const n)
      (f := HenkinConstStage.lift (Base := Base) (Const := Const) h)
      (Δ := Δ)
      (φ := φ)
      d)

theorem stageLift_closedTheoryProvable
    {m n : Nat} (h : m ≤ n)
    {Δ : List (ClosedFormula (HenkinConstStage Base Const m))}
    {φ : ClosedFormula (HenkinConstStage Base Const m)}
    (d : ExtDerivation (HenkinConstStage Base Const m) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) h))
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) h φ) := by
  exact stageLift_formulaProvable (Base := Base) (Const := Const) h d

theorem stageLift_formulaProvable_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstStage Base Const l) Γ)}
    {φ : Formula (HenkinConstStage Base Const l) Γ}
    (d : ExtDerivation (HenkinConstStage Base Const l) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map
        (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn)))
      (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
        (Nat.le_trans hlm hmn) φ) := by
  have d' :=
    stageLift_formulaProvable (Base := Base) (Const := Const) hmn
      (stageLift_formulaProvable (Base := Base) (Const := Const) hlm d)
  have hΔ :
      List.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn)
          (List.map (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hlm) Δ) =
        Δ.map
          (HenkinConstStage.liftFormula (Base := Base) (Const := Const)
            (Nat.le_trans hlm hmn)) := by
    induction Δ with
    | nil => rfl
    | cons ψ Δ ih =>
        simp [HenkinConstStage.liftFormula_comp
          (Base := Base) (Const := Const) hlm hmn]
  have hφ :
      HenkinConstStage.liftFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.liftFormula (Base := Base) (Const := Const) hlm φ) =
        HenkinConstStage.liftFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn) φ := by
    simpa using HenkinConstStage.liftFormula_comp
      (Base := Base) (Const := Const) hlm hmn φ
  exact hΔ ▸ hφ ▸ d'

theorem stageLift_closedTheoryProvable_comp
    {l m n : Nat} (hlm : l ≤ m) (hmn : m ≤ n)
    {Δ : List (ClosedFormula (HenkinConstStage Base Const l))}
    {φ : ClosedFormula (HenkinConstStage Base Const l)}
    (d : ExtDerivation (HenkinConstStage Base Const l) Δ φ) :
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn)))
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_trans hlm hmn) φ) := by
  have d' :=
    stageLift_closedTheoryProvable (Base := Base) (Const := Const) hmn
      (stageLift_closedTheoryProvable (Base := Base) (Const := Const) hlm d)
  have hΔ :
      List.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn)
          (List.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hlm) Δ) =
        Δ.map
          (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
            (Nat.le_trans hlm hmn)) := by
    induction Δ with
    | nil => rfl
    | cons ψ Δ ih =>
        simp [HenkinConstStage.liftClosedFormula_comp
          (Base := Base) (Const := Const) hlm hmn]
  have hφ :
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hlm φ) =
        HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
          (Nat.le_trans hlm hmn) φ := by
    simpa using HenkinConstStage.liftClosedFormula_comp
      (Base := Base) (Const := Const) hlm hmn φ
  exact hΔ ▸ hφ ▸ d'

def SupportedStageDerivation.liftTo
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    {n : Nat} (h : S.stage ≤ n) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  refine
    { stage := n
      context := S.context.map
        (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h)
      formula := HenkinConstStage.liftFormula (Base := Base) (Const := Const) h S.formula
      soundContext := ?_
      soundFormula := ?_
      deriv := ?_ }
  · calc
      List.map (liftFormula (Base := Base) (Const := Const))
          (List.map
            (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h)
            S.context) =
        List.map
          (fun ψ =>
            liftFormula (Base := Base) (Const := Const)
              (HenkinConstStage.liftFormula (Base := Base) (Const := Const) h ψ))
          S.context := by
            simp [List.map_map]
      _ =
        List.map
          (fun ψ => liftFormula (Base := Base) (Const := Const) ψ)
          S.context := by
            induction S.context with
            | nil => rfl
            | cons ψ Γ ih =>
                simp only [List.map]
                rw [HenkinConstInfinity.liftFormula_stageLift
                  (Base := Base) (Const := Const) h ψ, ih]
      _ = Δ := S.soundContext
  · exact (HenkinConstInfinity.liftFormula_stageLift
      (Base := Base) (Const := Const) h S.formula).trans S.soundFormula
  · exact stageLift_formulaProvable (Base := Base) (Const := Const) h S.deriv

theorem SupportedStageDerivation.liftTo_common_context
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    (Sψ : SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ) :
    (Sφ.liftTo (n := Sφ.stage + Sψ.stage)
      (Nat.le_add_right Sφ.stage Sψ.stage)).context =
      (Sψ.liftTo (n := Sφ.stage + Sψ.stage)
        (Nat.le_add_left Sψ.stage Sφ.stage)).context := by
  apply liftFormulaList_injective (Base := Base) (Const := Const)
    (n := Sφ.stage + Sψ.stage)
  exact
    ((Sφ.liftTo (n := Sφ.stage + Sψ.stage)
      (Nat.le_add_right Sφ.stage Sψ.stage)).soundContext).trans
      ((Sψ.liftTo (n := Sφ.stage + Sψ.stage)
        (Nat.le_add_left Sψ.stage Sφ.stage)).soundContext).symm

def SupportedStageDerivation.andI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ)
    (Sψ : SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.and φ ψ) := by
  let Tφ :=
    Sφ.liftTo (n := Sφ.stage + Sψ.stage)
      (Nat.le_add_right Sφ.stage Sψ.stage)
  let Tψ :=
    Sψ.liftTo (n := Sφ.stage + Sψ.stage)
      (Nat.le_add_left Sψ.stage Sφ.stage)
  have hctx : Tφ.context = Tψ.context :=
    SupportedStageDerivation.liftTo_common_context
      (Base := Base) (Const := Const) Sφ Sψ
  refine
    { stage := Tφ.stage
      context := Tφ.context
      formula := .and Tφ.formula Tψ.formula
      soundContext := Tφ.soundContext
      soundFormula := ?_
      deriv := ?_ }
  · simpa [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst,
      Tφ.soundFormula, Tψ.soundFormula]
  · have hψ :
        ExtDerivation (HenkinConstStage Base Const Tφ.stage) Tφ.context Tψ.formula := by
      simpa [hctx] using Tψ.deriv
    exact ExtDerivation.andI Tφ.deriv hψ

def SupportedStageDerivation.impE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Simp : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp φ ψ))
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ := by
  let Timp :=
    Simp.liftTo (n := Simp.stage + Sφ.stage)
      (Nat.le_add_right Simp.stage Sφ.stage)
  let Tφ :=
    Sφ.liftTo (n := Simp.stage + Sφ.stage)
      (Nat.le_add_left Sφ.stage Simp.stage)
  have hctx : Timp.context = Tφ.context :=
    SupportedStageDerivation.liftTo_common_context
      (Base := Base) (Const := Const) Simp Sφ
  let shp :=
    liftFormula_eq_imp_inv (Base := Base) (Const := Const) Timp.soundFormula
  let φ' := shp.antecedent
  let ψ' := shp.consequent
  have hshape : Timp.formula = .imp φ' ψ' := shp.shape
  have hφ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) φ' = φ :=
    shp.soundAntecedent
  have hψ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) ψ' = ψ :=
    shp.soundConsequent
  have hφEq : Tφ.formula = φ' :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Timp.stage)
      (Tφ.soundFormula.trans hφ.symm)
  refine
    { stage := Timp.stage
      context := Timp.context
      formula := ψ'
      soundContext := Timp.soundContext
      soundFormula := hψ
      deriv := ?_ }
  have himpDeriv :
      ExtDerivation (HenkinConstStage Base Const Timp.stage) Timp.context (.imp φ' ψ') := by
    simpa [hshape] using Timp.deriv
  have hφDeriv :
      ExtDerivation (HenkinConstStage Base Const Timp.stage) Timp.context φ' := by
    simpa [hctx, hφEq] using Tφ.deriv
  exact ExtDerivation.impE himpDeriv hφDeriv

def SupportedStageDerivation.notE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (Snot : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.not φ))
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.bot : Formula _ Γ) := by
  let Tnot :=
    Snot.liftTo (n := Snot.stage + Sφ.stage)
      (Nat.le_add_right Snot.stage Sφ.stage)
  let Tφ :=
    Sφ.liftTo (n := Snot.stage + Sφ.stage)
      (Nat.le_add_left Sφ.stage Snot.stage)
  have hctx : Tnot.context = Tφ.context :=
    SupportedStageDerivation.liftTo_common_context
      (Base := Base) (Const := Const) Snot Sφ
  let shp :=
    liftFormula_eq_not_inv (Base := Base) (Const := Const) Tnot.soundFormula
  let φ' := shp.body
  have hshape : Tnot.formula = .not φ' := shp.shape
  have hφ :
      HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) φ' = φ :=
    shp.soundBody
  have hφEq : Tφ.formula = φ' :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Tnot.stage)
      (Tφ.soundFormula.trans hφ.symm)
  refine
    { stage := Tnot.stage
      context := Tnot.context
      formula := .bot
      soundContext := Tnot.soundContext
      soundFormula := rfl
      deriv := ?_ }
  have hnotDeriv :
      ExtDerivation (HenkinConstStage Base Const Tnot.stage) Tnot.context (.not φ') := by
    simpa [hshape] using Tnot.deriv
  have hφDeriv :
      ExtDerivation (HenkinConstStage Base Const Tnot.stage) Tnot.context φ' := by
    simpa [hctx, hφEq] using Tφ.deriv
  exact ExtDerivation.notE hnotDeriv hφDeriv

def SupportedStageDerivation.impI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) (φ :: Δ) ψ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp φ ψ) := by
  let dec := S.decomposeConsContext
  let φ' := dec.head
  let Δ' := dec.tail
  have hctx : S.context = φ' :: Δ' := dec.shape
  have hφ :
      liftFormula (Base := Base) (Const := Const) φ' = φ := dec.soundHead
  have hΔ' :
      Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := dec.soundTail
  refine
    { stage := S.stage
      context := Δ'
      formula := .imp φ' S.formula
      soundContext := hΔ'
      soundFormula := ?_
      deriv := ?_ }
  · simpa [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst,
      hφ, S.soundFormula]
  · have hderiv :
        ExtDerivation (HenkinConstStage Base Const S.stage) (φ' :: Δ') S.formula := by
      simpa [hctx] using S.deriv
    exact ExtDerivation.impI hderiv

def SupportedStageDerivation.notI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const)
      (φ :: Δ) (.bot : Formula _ Γ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.not φ) := by
  let dec := S.decomposeConsContext
  let φ' := dec.head
  let Δ' := dec.tail
  have hctx : S.context = φ' :: Δ' := dec.shape
  have hφ :
      liftFormula (Base := Base) (Const := Const) φ' = φ := dec.soundHead
  have hΔ' :
      Δ'.map (liftFormula (Base := Base) (Const := Const)) = Δ := dec.soundTail
  refine
    { stage := S.stage
      context := Δ'
      formula := .not φ'
      soundContext := hΔ'
      soundFormula := ?_
      deriv := ?_ }
  · simpa [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst, hφ]
  · have hderiv :
        ExtDerivation (HenkinConstStage Base Const S.stage) (φ' :: Δ')
          (.bot : Formula (HenkinConstStage Base Const S.stage) Γ) := by
      have hbotEq : S.formula = (.bot : Formula (HenkinConstStage Base Const S.stage) Γ) :=
        liftFormula_injective (Base := Base) (Const := Const) (n := S.stage)
          (S.soundFormula.trans rfl.symm)
      simpa [hctx, hbotEq] using S.deriv
    exact ExtDerivation.notI hderiv

def SupportedStageDerivation.botE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sbot : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.bot : Formula _ Γ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ φ := by
  let Tbot :=
    Sbot.liftTo (n := Sbot.stage + (stageTerm (Base := Base) (Const := Const) φ).stage)
      (Nat.le_add_right Sbot.stage
        ((stageTerm (Base := Base) (Const := Const) φ).stage))
  let φ' :=
    stageFormulaTo (Base := Base) (Const := Const) φ
      (n := Tbot.stage)
      (Nat.le_add_left
        ((stageTerm (Base := Base) (Const := Const) φ).stage) Sbot.stage)
  refine
    { stage := Tbot.stage
      context := Tbot.context
      formula := φ'
      soundContext := Tbot.soundContext
      soundFormula := stageFormulaTo_sound (Base := Base) (Const := Const) φ
        (Nat.le_add_left
          ((stageTerm (Base := Base) (Const := Const) φ).stage) Sbot.stage)
      deriv := ?_ }
  have hbotEq : Tbot.formula = (.bot : Formula (HenkinConstStage Base Const Tbot.stage) Γ) :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Tbot.stage)
      (Tbot.soundFormula.trans rfl.symm)
  have hbotDeriv :
      ExtDerivation (HenkinConstStage Base Const Tbot.stage) Tbot.context
        (.bot : Formula (HenkinConstStage Base Const Tbot.stage) Γ) := by
    simpa [hbotEq] using Tbot.deriv
  exact ExtDerivation.botE hbotDeriv

def SupportedStageDerivation.orIL
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.or φ ψ) := by
  let Tφ :=
    Sφ.liftTo (n := Sφ.stage + (stageTerm (Base := Base) (Const := Const) ψ).stage)
      (Nat.le_add_right Sφ.stage
        ((stageTerm (Base := Base) (Const := Const) ψ).stage))
  let ψ' :=
    stageFormulaTo (Base := Base) (Const := Const) ψ
      (n := Tφ.stage)
      (Nat.le_add_left
        ((stageTerm (Base := Base) (Const := Const) ψ).stage) Sφ.stage)
  refine
    { stage := Tφ.stage
      context := Tφ.context
      formula := .or Tφ.formula ψ'
      soundContext := Tφ.soundContext
      soundFormula := ?_
      deriv := ?_ }
  · calc
      liftFormula (Base := Base) (Const := Const) (.or Tφ.formula ψ') =
          .or
            (liftFormula (Base := Base) (Const := Const) Tφ.formula)
            (liftFormula (Base := Base) (Const := Const) ψ') := by
              rfl
      _ = .or φ (liftFormula (Base := Base) (Const := Const) ψ') := by
            rw [Tφ.soundFormula]
      _ = .or φ ψ := by
            have hψ' :
                liftFormula (Base := Base) (Const := Const) ψ' = ψ := by
              unfold ψ'
              exact stageFormulaTo_sound (Base := Base) (Const := Const) ψ
                (Nat.le_add_left
                  ((stageTerm (Base := Base) (Const := Const) ψ).stage) Sφ.stage)
            rw [hψ']
  · exact ExtDerivation.orIL Tφ.deriv

def SupportedStageDerivation.orIR
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sψ : SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.or φ ψ) := by
  let Tψ :=
    Sψ.liftTo (n := (stageTerm (Base := Base) (Const := Const) φ).stage + Sψ.stage)
      (Nat.le_add_left Sψ.stage
        ((stageTerm (Base := Base) (Const := Const) φ).stage))
  let φ' :=
    stageFormulaTo (Base := Base) (Const := Const) φ
      (n := Tψ.stage)
      (Nat.le_add_right
        ((stageTerm (Base := Base) (Const := Const) φ).stage) Sψ.stage)
  refine
    { stage := Tψ.stage
      context := Tψ.context
      formula := .or φ' Tψ.formula
      soundContext := Tψ.soundContext
      soundFormula := ?_
      deriv := ?_ }
  · calc
      liftFormula (Base := Base) (Const := Const) (.or φ' Tψ.formula) =
          .or
            (liftFormula (Base := Base) (Const := Const) φ')
            (liftFormula (Base := Base) (Const := Const) Tψ.formula) := by
              rfl
      _ = .or (liftFormula (Base := Base) (Const := Const) φ') ψ := by
            rw [Tψ.soundFormula]
      _ = .or φ ψ := by
            have hφ' :
                liftFormula (Base := Base) (Const := Const) φ' = φ := by
              unfold φ'
              exact stageFormulaTo_sound (Base := Base) (Const := Const) φ
                (Nat.le_add_right
                  ((stageTerm (Base := Base) (Const := Const) φ).stage) Sψ.stage)
            rw [hφ']
  · exact ExtDerivation.orIR Tψ.deriv

def SupportedStageDerivation.orE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ ψ χ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sor : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.or φ ψ))
    (Sφ : SupportedStageDerivation (Base := Base) (Const := Const) (φ :: Δ) χ)
    (Sψ : SupportedStageDerivation (Base := Base) (Const := Const) (ψ :: Δ) χ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ χ := by
  let n := Sor.stage + (Sφ.stage + Sψ.stage)
  let Tor := Sor.liftTo (n := n)
    (Nat.le_add_right Sor.stage (Sφ.stage + Sψ.stage))
  let Tφ := Sφ.liftTo (n := n)
    (Nat.le_trans (Nat.le_add_left Sφ.stage Sor.stage)
      (by simpa [n, Nat.add_assoc] using Nat.le_add_right (Sor.stage + Sφ.stage) Sψ.stage))
  let Tψ := Sψ.liftTo (n := n)
    (Nat.le_trans
      (Nat.le_add_left Sψ.stage Sφ.stage)
      (by simpa [n] using Nat.le_add_left (Sφ.stage + Sψ.stage) Sor.stage))
  let shpor := liftFormula_eq_or_inv (Base := Base) (Const := Const) Tor.soundFormula
  let decφ := Tφ.decomposeConsContext
  let decψ := Tψ.decomposeConsContext
  have hctxφTail : decφ.tail = Tor.context :=
    liftFormulaList_injective (Base := Base) (Const := Const) (n := n)
      (decφ.soundTail.trans Tor.soundContext.symm)
  have hctxψTail : decψ.tail = Tor.context :=
    liftFormulaList_injective (Base := Base) (Const := Const) (n := n)
      (decψ.soundTail.trans Tor.soundContext.symm)
  have hleftEq : decφ.head = shpor.left :=
    liftFormula_injective (Base := Base) (Const := Const) (n := n)
      (decφ.soundHead.trans shpor.soundLeft.symm)
  have hrightEq : decψ.head = shpor.right :=
    liftFormula_injective (Base := Base) (Const := Const) (n := n)
      (decψ.soundHead.trans shpor.soundRight.symm)
  have hχEq : Tψ.formula = Tφ.formula :=
    liftFormula_injective (Base := Base) (Const := Const) (n := n)
      (Tψ.soundFormula.trans Tφ.soundFormula.symm)
  refine
    { stage := n
      context := Tor.context
      formula := Tφ.formula
      soundContext := Tor.soundContext
      soundFormula := Tφ.soundFormula
      deriv := ?_ }
  have horDeriv :
      ExtDerivation (HenkinConstStage Base Const n) Tor.context (.or shpor.left shpor.right) := by
    simpa [shpor.shape] using Tor.deriv
  have hφDeriv :
      ExtDerivation (HenkinConstStage Base Const n) (shpor.left :: Tor.context) Tφ.formula := by
    have hctx : Tφ.context = shpor.left :: Tor.context := by
      simpa [hctxφTail, hleftEq] using decφ.shape
    simpa [hctx] using Tφ.deriv
  have hψDeriv :
      ExtDerivation (HenkinConstStage Base Const n) (shpor.right :: Tor.context) Tφ.formula := by
    have hctx : Tψ.context = shpor.right :: Tor.context := by
      simpa [hctxψTail, hrightEq] using decψ.shape
    simpa [hctx, hχEq] using Tψ.deriv
  exact ExtDerivation.orE horDeriv hφDeriv hψDeriv

def SupportedStageDerivation.allE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ : Ty Base}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    (t : Term (HenkinConstInfinity Base Const) Γ σ)
    (Sall : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.all φ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (instantiate (Base := Base) t φ) := by
  let Tall :=
    Sall.liftTo (n := Sall.stage + (stageTerm (Base := Base) (Const := Const) t).stage)
      (Nat.le_add_right Sall.stage
        ((stageTerm (Base := Base) (Const := Const) t).stage))
  let t' :=
    stageTermTo (Base := Base) (Const := Const) t
      (n := Tall.stage)
      (Nat.le_add_left
        ((stageTerm (Base := Base) (Const := Const) t).stage) Sall.stage)
  let shp := liftFormula_eq_all_inv (Base := Base) (Const := Const) (σ := σ) Tall.soundFormula
  let body' := shp.body
  refine
    { stage := Tall.stage
      context := Tall.context
      formula := instantiate (Base := Base) t' body'
      soundContext := Tall.soundContext
      soundFormula := ?_
      deriv := ?_ }
  · calc
      liftFormula (Base := Base) (Const := Const) (instantiate (Base := Base) t' body') =
        instantiate (Base := Base)
          (liftTerm (Base := Base) (Const := Const) t')
          (liftFormula (Base := Base) (Const := Const) body') := by
            simpa using liftFormula_instantiate
              (Base := Base) (Const := Const) t' body'
      _ = instantiate (Base := Base) t
          (liftFormula (Base := Base) (Const := Const) body') := by
            rw [stageTermTo_sound (Base := Base) (Const := Const) t
              (h := Nat.le_add_left
                ((stageTerm (Base := Base) (Const := Const) t).stage) Sall.stage)]
      _ = instantiate (Base := Base) t φ := by
            rw [shp.soundBody]
  · have hallDeriv :
        ExtDerivation (HenkinConstStage Base Const Tall.stage) Tall.context (.all body') := by
      simpa [shp.shape] using Tall.deriv
    exact ExtDerivation.allE t' hallDeriv

def SupportedStageDerivation.exI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ : Ty Base}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    (t : Term (HenkinConstInfinity Base Const) Γ σ)
    (Sinst : SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (instantiate (Base := Base) t φ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.ex φ) := by
  let n :=
    Sinst.stage +
      ((stageTerm (Base := Base) (Const := Const) φ).stage +
        (stageTerm (Base := Base) (Const := Const) t).stage)
  let Tinst := Sinst.liftTo (n := n)
    (Nat.le_add_right Sinst.stage
      ((stageTerm (Base := Base) (Const := Const) φ).stage +
        (stageTerm (Base := Base) (Const := Const) t).stage))
  let t' :=
    stageTermTo (Base := Base) (Const := Const) t
      (n := n)
      (by
        simpa [n, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.le_add_left
            ((stageTerm (Base := Base) (Const := Const) t).stage)
            (Sinst.stage + (stageTerm (Base := Base) (Const := Const) φ).stage))
  let body' :=
    stageFormulaTo (Base := Base) (Const := Const) φ
      (n := n)
      (by
        exact Nat.le_trans
          (Nat.le_add_left
            ((stageTerm (Base := Base) (Const := Const) φ).stage)
            Sinst.stage)
          (by
            simpa [n, Nat.add_assoc] using
              Nat.le_add_right
                (Sinst.stage + (stageTerm (Base := Base) (Const := Const) φ).stage)
                ((stageTerm (Base := Base) (Const := Const) t).stage)))
  have hinstEq :
      Tinst.formula = instantiate (Base := Base) t' body' := by
    apply liftFormula_injective (Base := Base) (Const := Const) (n := n)
    calc
      liftFormula (Base := Base) (Const := Const) Tinst.formula =
        instantiate (Base := Base) t φ := Tinst.soundFormula
      _ =
        liftFormula (Base := Base) (Const := Const)
          (instantiate (Base := Base) t' body') := by
            symm
            calc
              liftFormula (Base := Base) (Const := Const)
                  (instantiate (Base := Base) t' body') =
                instantiate (Base := Base)
                  (liftTerm (Base := Base) (Const := Const) t')
                  (liftFormula (Base := Base) (Const := Const) body') := by
                    simpa using liftFormula_instantiate
                      (Base := Base) (Const := Const) t' body'
              _ = instantiate (Base := Base) t
                  (liftFormula (Base := Base) (Const := Const) body') := by
                    have ht' :
                        liftTerm (Base := Base) (Const := Const) t' = t :=
                      stageTermTo_sound (Base := Base) (Const := Const) t
                        (n := n)
                        (h := by
                          simpa [n, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                            Nat.le_add_left
                              ((stageTerm (Base := Base) (Const := Const) t).stage)
                              (Sinst.stage + (stageTerm (Base := Base) (Const := Const) φ).stage))
                    simpa [ht']
              _ = instantiate (Base := Base) t φ := by
                    rw [stageFormulaTo_sound (Base := Base) (Const := Const) φ
                      (h := by
                        exact Nat.le_trans
                          (Nat.le_add_left
                            ((stageTerm (Base := Base) (Const := Const) φ).stage)
                            Sinst.stage)
                          (by
                            simpa [n, Nat.add_assoc] using
                              Nat.le_add_right
                                (Sinst.stage +
                                  (stageTerm (Base := Base) (Const := Const) φ).stage)
                                ((stageTerm (Base := Base) (Const := Const) t).stage)))]
  refine
    { stage := n
      context := Tinst.context
      formula := .ex body'
      soundContext := Tinst.soundContext
      soundFormula := ?_
      deriv := ?_ }
  · simpa [HenkinConstInfinity.liftFormula, liftFormula, Mettapedia.Logic.HOL.mapConst]
      using stageFormulaTo_sound (Base := Base) (Const := Const) φ
        (n := n)
        (h := by
          exact Nat.le_trans
            (Nat.le_add_left
              ((stageTerm (Base := Base) (Const := Const) φ).stage)
              Sinst.stage)
            (by
              simpa [n, Nat.add_assoc] using
                Nat.le_add_right
                  (Sinst.stage + (stageTerm (Base := Base) (Const := Const) φ).stage)
                  ((stageTerm (Base := Base) (Const := Const) t).stage)))
  · have hinstDeriv :
        ExtDerivation (HenkinConstStage Base Const n) Tinst.context
          (instantiate (Base := Base) t' body') := by
      simpa [hinstEq] using Tinst.deriv
    exact ExtDerivation.exI t' hinstDeriv

/-- Every cumulative-signature formula has a designated witness term one stage above some support stage. -/
theorem exists_stage_witness_term {σ : Ty Base}
    (φ : Formula (HenkinConstInfinity Base Const) [σ]) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) [σ],
      liftFormula (Base := Base) (Const := Const) φ' = φ ∧
      ∃ t : ClosedTerm (HenkinConstInfinity Base Const) σ,
        t = liftTerm (Base := Base) (Const := Const)
          (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ') := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  refine ⟨n, φ', hφ, ?_⟩
  refine ⟨liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ'), rfl⟩

/-- Every cumulative-signature formula has a designated counterexample term one stage above some support stage. -/
theorem exists_stage_counterexample_term {σ : Ty Base}
    (φ : Formula (HenkinConstInfinity Base Const) [σ]) :
    ∃ n, ∃ φ' : Formula (HenkinConstStage Base Const n) [σ],
      liftFormula (Base := Base) (Const := Const) φ' = φ ∧
      ∃ t : ClosedTerm (HenkinConstInfinity Base Const) σ,
        t = liftTerm (Base := Base) (Const := Const)
          (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ') := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  refine ⟨n, φ', hφ, ?_⟩
  refine ⟨liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ'), rfl⟩

/-- The `allI` constructor for supported stage derivations.
    Given a supported stage derivation of `weakenHyps Δ ⊢ φ`, produce
    a supported stage derivation of `Δ ⊢ .all φ`.

    This uses `mapConst_weaken_preimage` (the separation lemma) to
    recover the un-weakened stage-n context from the weakened one. -/
noncomputable def SupportedStageDerivation.allI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ : Ty Base}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    (S : SupportedStageDerivation (Base := Base) (Const := Const)
      (weakenHyps (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) Δ) φ) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.all φ) := by
  -- S.context is at stage n in context (σ :: Γ)
  -- S.soundContext : S.context.map liftFormula = weakenHyps Δ = Δ.map weaken
  -- By the separation lemma, recover un-weakened context
  have hctx : S.context.map (liftFormula (Base := Base) (Const := Const)) =
      Δ.map (weaken (Base := Base) (σ := σ)) := by
    simpa [weakenHyps] using S.soundContext
  let pre :=
    Mettapedia.Logic.HOL.map_mapConst_eq_map_weaken_preimage
      (Base := Base) (Const := HenkinConstStage Base Const S.stage)
      (Const' := HenkinConstInfinity Base Const)
      (ofStage (Base := Base) (Const := Const))
      S.context Δ hctx
  let Θ := pre.choose
  have hΘ := pre.choose_spec
  refine
    { stage := S.stage
      context := Θ
      formula := .all S.formula
      soundContext := hΘ.2
      soundFormula := ?_
      deriv := ?_ }
  · -- liftFormula (.all S.formula) = .all φ
    simp [liftFormula, mapConst, S.soundFormula]
  · -- ExtDerivation (Stage n) Θ (.all S.formula)
    apply ExtDerivation.allI (σ := σ)
    show ExtDerivation _ (weakenHyps (Base := Base) (σ := σ) Θ) S.formula
    rw [show weakenHyps (Base := Base) (σ := σ) Θ = S.context from by
      simp [weakenHyps]; exact hΘ.1.symm]
    exact S.deriv

/-- The `eqLam` constructor: from `weakenHyps Δ ⊢ t = u`, derive `Δ ⊢ lam t = lam u`.
    Same weakening-preimage pattern as `allI`. -/
noncomputable def SupportedStageDerivation.eqLam
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    {t u : Term (HenkinConstInfinity Base Const) (σ :: Γ) τ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const)
      (weakenHyps (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) Δ)
      (.eq t u)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (.eq (.lam t) (.lam u)) := by
  -- Recover un-weakened context
  have hctx : S.context.map (liftFormula (Base := Base) (Const := Const)) =
      Δ.map (weaken (Base := Base) (σ := σ)) := by
    simpa [weakenHyps] using S.soundContext
  let pre :=
    Mettapedia.Logic.HOL.map_mapConst_eq_map_weaken_preimage
      (Base := Base) (Const := HenkinConstStage Base Const S.stage)
      (Const' := HenkinConstInfinity Base Const)
      (ofStage (Base := Base) (Const := Const))
      S.context Δ hctx
  let Θ := pre.choose
  have hΘ := pre.choose_spec
  -- Recover eq sub-terms from the formula
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
  refine
    { stage := S.stage
      context := Θ
      formula := .eq (.lam eqW.left) (.lam eqW.right)
      soundContext := hΘ.2
      soundFormula := ?_
      deriv := ?_ }
  · simp [liftFormula, liftTerm, mapConst, eqW.soundLeft, eqW.soundRight]
  · apply ExtDerivation.eqLam (σ := σ)
    show ExtDerivation _ (weakenHyps (Base := Base) (σ := σ) Θ) (.eq eqW.left eqW.right)
    rw [show weakenHyps (Base := Base) (σ := σ) Θ = S.context from by
      simp [weakenHyps]; exact hΘ.1.symm]
    rw [show (.eq eqW.left eqW.right : Formula _ _) = S.formula from eqW.shape.symm]
    exact S.deriv

noncomputable def SupportedStageDerivation.exE
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ : Ty Base}
    {φ : Formula (HenkinConstInfinity Base Const) (σ :: Γ)}
    {ψ : Formula (HenkinConstInfinity Base Const) Γ}
    (Sex : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.ex φ))
    (Sbody : SupportedStageDerivation (Base := Base) (Const := Const)
      (φ :: weakenHyps (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) Δ)
      (weaken (Base := Base) (Const := HenkinConstInfinity Base Const) (σ := σ) ψ)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ ψ := by
  -- Lift to common stage
  let Tex :=
    Sex.liftTo (n := Sex.stage + Sbody.stage)
      (Nat.le_add_right Sex.stage Sbody.stage)
  let Tbody :=
    Sbody.liftTo (n := Sex.stage + Sbody.stage)
      (Nat.le_add_left Sbody.stage Sex.stage)
  -- Recover ex shape
  let exW := liftFormula_eq_ex_inv (Base := Base) (Const := Const) Tex.soundFormula
  -- Decompose body context: φ :: weakenHyps Δ
  let bodyCtxW := Tbody.decomposeConsContext
  -- Recover un-weakened tail context
  have hTail : bodyCtxW.tail.map (liftFormula (Base := Base) (Const := Const)) =
      Δ.map (weaken (Base := Base) (σ := σ)) := by
    simpa [weakenHyps] using bodyCtxW.soundTail
  let tailPre :=
    Mettapedia.Logic.HOL.map_mapConst_eq_map_weaken_preimage
      (Base := Base) (Const := HenkinConstStage Base Const Tbody.stage)
      (Const' := HenkinConstInfinity Base Const)
      (ofStage (Base := Base) (Const := Const))
      bodyCtxW.tail Δ hTail
  let Θ := tailPre.choose
  have hΘ := tailPre.choose_spec
  -- Recover un-weakened formula
  let wkPre :=
    Mettapedia.Logic.HOL.mapConst_weaken_preimage
      (Base := Base)
      (Const := HenkinConstStage Base Const Tbody.stage)
      (Const' := HenkinConstInfinity Base Const)
      (ofStage (Base := Base) (Const := Const))
      Tbody.soundFormula
  let ψ' := wkPre.choose
  have hψ' := wkPre.choose_spec
  -- Align Tex.context with Θ (both map to Δ via liftFormula at same stage)
  have hCtxAlign : Tex.context = Θ :=
    liftFormulaList_injective (Base := Base) (Const := Const)
      (n := Tex.stage)
      (Tex.soundContext.trans hΘ.2.symm)
  -- Align bodyCtxW.head with exW.body (both lift to φ)
  have hHeadAlign : bodyCtxW.head = exW.body :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Tbody.stage)
      (bodyCtxW.soundHead.trans exW.soundBody.symm)
  refine
    { stage := Tbody.stage
      context := Θ
      formula := ψ'
      soundContext := hΘ.2
      soundFormula := hψ'.2
      deriv := ?_ }
  -- Apply ExtDerivation.exE with two rewritten sub-derivations
  apply ExtDerivation.exE (φ := exW.body)
  · -- d1 : ExtDerivation (Stage n) Θ (.ex exW.body)
    rw [show (.ex exW.body : Formula _ _) = Tex.formula from exW.shape.symm]
    rw [show Θ = Tex.context from hCtxAlign.symm]
    exact Tex.deriv
  · -- d2 : ExtDerivation (Stage n) (exW.body :: weakenHyps Θ) (weaken ψ')
    rw [show weaken (Base := Base) (σ := σ) ψ' = Tbody.formula from hψ'.1.symm]
    rw [show (exW.body :: weakenHyps (Base := Base) (σ := σ) Θ) = Tbody.context from by
      rw [bodyCtxW.shape]
      congr 1
      · exact hHeadAlign.symm
      · simp [weakenHyps]; exact hΘ.1.symm]
    exact Tbody.deriv

/-- Same-context equality constructors. These follow the propositional pattern
    (no weakening inversion needed). -/

theorem supportedStageDerivation_eqRefl
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ τ) :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq t t)) := by
  let S := stageJudgement (Base := Base) (Const := Const) Δ (.eq t t)
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        have hshape : S.formula = .eq eqW.left eqW.right := eqW.shape
        have hleft : eqW.left = eqW.right := by
          apply liftTerm_injective (Base := Base) (Const := Const) (n := S.stage)
          rw [eqW.soundLeft, eqW.soundRight]
        simpa [hshape, hleft] using ExtDerivation.eqRefl eqW.right }⟩

noncomputable def SupportedStageDerivation.eqSymm
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {τ : Ty Base}
    {t u : Term (HenkinConstInfinity Base Const) Γ τ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq t u)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq u t) := by
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
  refine
    { stage := S.stage
      context := S.context
      formula := .eq eqW.right eqW.left
      soundContext := S.soundContext
      soundFormula := by simp [liftFormula, liftTerm, mapConst, eqW.soundRight, eqW.soundLeft]
      deriv := ?_ }
  apply ExtDerivation.eqSymm
  rw [show (.eq eqW.left eqW.right : Formula _ _) = S.formula from eqW.shape.symm]
  exact S.deriv

noncomputable def SupportedStageDerivation.eqTrans
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {τ : Ty Base}
    {t u v : Term (HenkinConstInfinity Base Const) Γ τ}
    (Stu : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq t u))
    (Suv : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq u v)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq t v) := by
  let Ttu :=
    Stu.liftTo (n := Stu.stage + Suv.stage)
      (Nat.le_add_right Stu.stage Suv.stage)
  let Tuv :=
    Suv.liftTo (n := Stu.stage + Suv.stage)
      (Nat.le_add_left Suv.stage Stu.stage)
  have hctx : Ttu.context = Tuv.context :=
    SupportedStageDerivation.liftTo_common_context
      (Base := Base) (Const := Const) Stu Suv
  let eqtu := liftFormula_eq_eq_inv (Base := Base) (Const := Const) Ttu.soundFormula
  let equv := liftFormula_eq_eq_inv (Base := Base) (Const := Const) Tuv.soundFormula
  have huEq : eqtu.right = equv.left := by
    apply liftTerm_injective (Base := Base) (Const := Const) (n := Ttu.stage)
    rw [eqtu.soundRight, equv.soundLeft]
  refine
    { stage := Ttu.stage
      context := Ttu.context
      formula := .eq eqtu.left equv.right
      soundContext := Ttu.soundContext
      soundFormula := by
        simp [liftFormula, liftTerm, mapConst, eqtu.soundLeft, equv.soundRight]
      deriv := ?_ }
  apply ExtDerivation.eqTrans (u := eqtu.right)
  · rw [show (.eq eqtu.left eqtu.right : Formula _ _) = Ttu.formula from eqtu.shape.symm]
    exact Ttu.deriv
  · rw [huEq]
    have hd : ExtDerivation _ Ttu.context Tuv.formula := by simpa [hctx] using Tuv.deriv
    rw [show (.eq equv.left equv.right : Formula _ _) = Tuv.formula from equv.shape.symm]
    exact hd

noncomputable def SupportedStageDerivation.funExt
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    {f g : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ)}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (.all (.eq (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))
                 (.app (weaken (Base := Base) (σ := σ) g) (.var .vz))))) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq f g) := by
  -- Invert: S.formula lifts to .all(.eq(.app(weaken f) vz)(.app(weaken g) vz))
  -- S.formula = .all body' where body' lifts to .eq(.app(weaken f) vz)(.app(weaken g) vz)
  let allW := liftFormula_eq_all_inv (Base := Base) (Const := Const) (σ := σ)
    S.soundFormula
  -- allW.body lifts to .eq(.app(weaken f) vz)(.app(weaken g) vz)
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) allW.soundBody
  -- eqW.left lifts to .app(weaken f)(vz), eqW.right lifts to .app(weaken g)(vz)
  -- Recover stage-n f' from eqW.left via app+weaken inversion
  -- eqW.left : Term (Stage n) (σ :: Γ) τ, liftTerm eqW.left = .app (weaken f) vz
  -- So eqW.left must be .app (weaken f') vz for some f'
  -- Similarly for eqW.right
  -- Use mapConst_weaken_preimage on the app sub-terms
  -- This is getting deeply nested. Use stageTermTo for f and g instead.
  let n := S.stage + ((stageTerm (Base := Base) (Const := Const) f).stage +
    (stageTerm (Base := Base) (Const := Const) g).stage)
  let T := S.liftTo (n := n) (Nat.le_add_right S.stage _)
  let f' := stageTermTo (Base := Base) (Const := Const) f (n := n)
    (by omega)
  let g' := stageTermTo (Base := Base) (Const := Const) g (n := n)
    (by omega)
  have hfEq : liftTerm (Base := Base) (Const := Const) f' = f :=
    stageTermTo_sound (Base := Base) (Const := Const) f (h := by omega)
  have hgEq : liftTerm (Base := Base) (Const := Const) g' = g :=
    stageTermTo_sound (Base := Base) (Const := Const) g (h := by omega)
  -- T.formula lifts to .all(.eq(.app(weaken f) vz)(.app(weaken g) vz))
  -- We need T.formula = .all(.eq(.app(weaken f') vz)(.app(weaken g') vz))
  have hFormulaEq : T.formula =
      (.all (.eq (.app (weaken (Base := Base) (σ := σ) f') (.var .vz))
                 (.app (weaken (Base := Base) (σ := σ) g') (.var .vz)))) := by
    apply liftFormula_injective (Base := Base) (Const := Const) (n := n)
    simp [liftFormula, liftTerm, mapConst, mapConst_weaken,
      hfEq, hgEq, T.soundFormula]
  refine
    { stage := n
      context := T.context
      formula := .eq f' g'
      soundContext := T.soundContext
      soundFormula := by simp [liftFormula, liftTerm, mapConst, hfEq, hgEq]
      deriv := ?_ }
  apply ExtDerivation.funExt (σ := σ)
  rw [hFormulaEq.symm]
  exact T.deriv

-- eqPropI: from Δ ⊢ p → q and Δ ⊢ q → p, derive Δ ⊢ p = q (2 sub-derivations, like andI)
noncomputable def SupportedStageDerivation.eqPropI
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {p q : Formula (HenkinConstInfinity Base Const) Γ}
    (Spq : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp p q))
    (Sqp : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp q p)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq p q) := by
  let Tpq := Spq.liftTo (n := Spq.stage + Sqp.stage) (Nat.le_add_right _ _)
  let Tqp := Sqp.liftTo (n := Spq.stage + Sqp.stage) (Nat.le_add_left _ _)
  have hctx := SupportedStageDerivation.liftTo_common_context (Base := Base) (Const := Const) Spq Sqp
  let shpPQ := liftFormula_eq_imp_inv (Base := Base) (Const := Const) Tpq.soundFormula
  let shpQP := liftFormula_eq_imp_inv (Base := Base) (Const := Const) Tqp.soundFormula
  have hpEq : shpPQ.antecedent = shpQP.consequent :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Tpq.stage)
      (shpPQ.soundAntecedent.trans shpQP.soundConsequent.symm)
  have hqEq : shpPQ.consequent = shpQP.antecedent :=
    liftFormula_injective (Base := Base) (Const := Const) (n := Tpq.stage)
      (shpPQ.soundConsequent.trans shpQP.soundAntecedent.symm)
  refine
    { stage := Tpq.stage
      context := Tpq.context
      formula := .eq shpPQ.antecedent shpPQ.consequent
      soundContext := Tpq.soundContext
      soundFormula := by simp [liftFormula, liftTerm, mapConst, shpPQ.soundAntecedent, shpPQ.soundConsequent]
      deriv := ?_ }
  apply ExtDerivation.eqPropI
  · simpa [shpPQ.shape] using Tpq.deriv
  · rw [hpEq, hqEq]
    rw [show (.imp shpQP.antecedent shpQP.consequent : Formula _ _) = Tqp.formula
        from shpQP.shape.symm]
    rw [show Tpq.context = Tqp.context from hctx]
    exact Tqp.deriv

-- eqPropEL: from Δ ⊢ p = q, derive Δ ⊢ p → q (1 sub-derivation, like andEL)
noncomputable def SupportedStageDerivation.eqPropEL
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {p q : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq p q)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp p q) := by
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
  refine
    { stage := S.stage
      context := S.context
      formula := .imp eqW.left eqW.right
      soundContext := S.soundContext
      soundFormula := by simp [liftFormula, liftTerm, mapConst, eqW.soundLeft, eqW.soundRight]
      deriv := ?_ }
  apply ExtDerivation.eqPropEL
  rw [show (.eq eqW.left eqW.right : Formula _ _) = S.formula from eqW.shape.symm]
  exact S.deriv

-- eqPropER: from Δ ⊢ p = q, derive Δ ⊢ q → p (like eqPropEL)
noncomputable def SupportedStageDerivation.eqPropER
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {p q : Formula (HenkinConstInfinity Base Const) Γ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq p q)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ (.imp q p) := by
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
  refine
    { stage := S.stage
      context := S.context
      formula := .imp eqW.right eqW.left
      soundContext := S.soundContext
      soundFormula := by simp [liftFormula, liftTerm, mapConst, eqW.soundLeft, eqW.soundRight]
      deriv := ?_ }
  apply ExtDerivation.eqPropER
  rw [show (.eq eqW.left eqW.right : Formula _ _) = S.formula from eqW.shape.symm]
  exact S.deriv

-- eqApp: from Δ ⊢ f = g, derive Δ ⊢ f t = g t (1 sub-derivation + term, like allE)
noncomputable def SupportedStageDerivation.eqApp
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    {f g : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ)}
    (t : Term (HenkinConstInfinity Base Const) Γ σ)
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq f g)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (.eq (.app f t) (.app g t)) := by
  let n := S.stage + (stageTerm (Base := Base) (Const := Const) t).stage
  let T := S.liftTo (n := n) (Nat.le_add_right _ _)
  let t' := stageTermTo (Base := Base) (Const := Const) t (n := n) (Nat.le_add_left _ _)
  have htEq := stageTermTo_sound (Base := Base) (Const := Const) t (h := Nat.le_add_left _ S.stage)
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) T.soundFormula
  refine
    { stage := n
      context := T.context
      formula := .eq (.app eqW.left t') (.app eqW.right t')
      soundContext := T.soundContext
      soundFormula := by
        show liftFormula _ = _
        simp only [liftFormula, liftTerm, mapConst]
        congr 1 <;> (congr 1 <;> first | exact eqW.soundLeft | exact eqW.soundRight | exact htEq)
      deriv := ?_ }
  apply ExtDerivation.eqApp t'
  rw [show (.eq eqW.left eqW.right : Formula _ _) = T.formula from eqW.shape.symm]
  exact T.deriv

-- eqAppArg: from Δ ⊢ t = u, derive Δ ⊢ f t = f u (1 sub-derivation + term)
noncomputable def SupportedStageDerivation.eqAppArg
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    (f : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ))
    {t u : Term (HenkinConstInfinity Base Const) Γ σ}
    (S : SupportedStageDerivation (Base := Base) (Const := Const) Δ (.eq t u)) :
    SupportedStageDerivation (Base := Base) (Const := Const) Δ
      (.eq (.app f t) (.app f u)) := by
  let n := S.stage + (stageTerm (Base := Base) (Const := Const) f).stage
  let T := S.liftTo (n := n) (Nat.le_add_right _ _)
  let f' := stageTermTo (Base := Base) (Const := Const) f (n := n) (Nat.le_add_left _ _)
  have hfEq := stageTermTo_sound (Base := Base) (Const := Const) f (h := Nat.le_add_left _ S.stage)
  let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) T.soundFormula
  refine
    { stage := n
      context := T.context
      formula := .eq (.app f' eqW.left) (.app f' eqW.right)
      soundContext := T.soundContext
      soundFormula := by
        show liftFormula _ = _
        simp only [liftFormula, liftTerm, mapConst]
        congr 1 <;> (congr 1 <;> first | exact hfEq | exact eqW.soundLeft | exact eqW.soundRight)
      deriv := ?_ }
  apply ExtDerivation.eqAppArg f'
  rw [show (.eq eqW.left eqW.right : Formula _ _) = T.formula from eqW.shape.symm]
  exact T.deriv

-- beta: Δ ⊢ (λu) t = u[t] (like eqRefl: use stageJudgement, injectivity, no sub-derivations)
theorem supportedStageDerivation_beta
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    (t : Term (HenkinConstInfinity Base Const) Γ σ)
    (u : Term (HenkinConstInfinity Base Const) (σ :: Γ) τ) :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ
        (.eq (.app (.lam u) t) (instantiate (Base := Base) t u))) := by
  let φ := (.eq (.app (.lam u) t) (instantiate (Base := Base) t u) :
    Formula (HenkinConstInfinity Base Const) Γ)
  let S := stageJudgement (Base := Base) (Const := Const) Δ φ
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        -- Nested inversion: eq → app → lam
        let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
        let appW := liftTerm_eq_app_inv (Base := Base) (Const := Const) eqW.soundLeft
        let lamW := liftTerm_eq_lam_inv (Base := Base) (Const := Const) appW.soundFn
        -- eqW.right lifts to instantiate t u
        -- appW.arg lifts to t, lamW.stageBody lifts to u
        -- So eqW.right = instantiate appW.arg lamW.stageBody by injectivity
        have hRight : eqW.right = instantiate (Base := Base) appW.arg lamW.stageBody := by
          apply liftTerm_injective (Base := Base) (Const := Const) (n := S.stage)
          rw [eqW.soundRight]
          change _ = mapConst (ofStage (Base := Base) (Const := Const))
            (instantiate (Base := Base) appW.arg lamW.stageBody)
          rw [mapConst_instantiate]
          congr 1
          · exact appW.soundArg.symm
          · exact lamW.soundBody.symm
        simpa [eqW.shape, appW.shape, lamW.shape, hRight] using
          ExtDerivation.beta appW.arg lamW.stageBody }⟩

-- eta: Δ ⊢ (λ(weaken f) x) = f (like eqRefl)
theorem supportedStageDerivation_eta
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {σ τ : Ty Base}
    (f : Term (HenkinConstInfinity Base Const) Γ (σ ⇒ τ)) :
    Nonempty
      (SupportedStageDerivation (Base := Base) (Const := Const) Δ
        (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f)) := by
  let φ := (.eq (.lam (.app (weaken (Base := Base) (σ := σ) f) (.var .vz))) f :
    Formula (HenkinConstInfinity Base Const) Γ)
  let S := stageJudgement (Base := Base) (Const := Const) Δ φ
  exact ⟨
    { stage := S.stage
      context := S.context
      formula := S.formula
      soundContext := S.soundContext
      soundFormula := S.soundFormula
      deriv := by
        -- Nested inversion: eq → lam → app, then weaken preimage
        let eqW := liftFormula_eq_eq_inv (Base := Base) (Const := Const) S.soundFormula
        let lamW := liftTerm_eq_lam_inv (Base := Base) (Const := Const) eqW.soundLeft
        let appW := liftTerm_eq_app_inv (Base := Base) (Const := Const) lamW.soundBody
        -- appW.arg lifts to .var .vz
        have hArg : appW.arg = .var .vz := by
          apply liftTerm_injective (Base := Base) (Const := Const) (n := S.stage)
          simpa [liftTerm, mapConst] using appW.soundArg
        -- appW.fn lifts to weaken f — recover f' via weaken preimage
        let wkPre := Mettapedia.Logic.HOL.mapConst_weaken_preimage
          (Base := Base) (Const := HenkinConstStage Base Const S.stage)
          (Const' := HenkinConstInfinity Base Const)
          (ofStage (Base := Base) (Const := Const))
          appW.soundFn
        let f' := wkPre.choose
        have hf' := wkPre.choose_spec
        -- eqW.right lifts to f — so eqW.right = f' by injectivity
        have hRight : eqW.right = f' :=
          liftTerm_injective (Base := Base) (Const := Const) (n := S.stage)
            (eqW.soundRight.trans hf'.2.symm)
        -- S.formula = .eq (.lam (.app (weaken f') (.var .vz))) f'
        have hShape : S.formula =
            .eq (.lam (.app (weaken (Base := Base) (σ := σ) f') (.var .vz))) f' := by
          conv_lhs => rw [eqW.shape]
          congr 1
          · rw [lamW.shape]; congr 1
            rw [appW.shape]; congr 1
            exact hf'.1
        simpa [hShape] using ExtDerivation.eta f' }⟩

/-- The main engine theorem: every derivation in the cumulative Henkin
    language has a finite-stage support. This is the induction on
    `ExtDerivation` that the entire reflection pipeline depends on. -/
theorem supportedStageDerivation_of_deriv
    {Γ : Ctx Base}
    {Δ : List (Formula (HenkinConstInfinity Base Const) Γ)}
    {φ : Formula (HenkinConstInfinity Base Const) Γ}
    (d : ExtDerivation (HenkinConstInfinity Base Const) Δ φ) :
    Nonempty (SupportedStageDerivation (Base := Base) (Const := Const) Δ φ) := by
  induction d with
  | hyp hmem => exact supportedStageDerivation_hyp hmem
  | topI => exact supportedStageDerivation_topI
  | botE _ ih => exact ⟨(ih.some).botE⟩
  | andI _ _ ihφ ihψ => exact ⟨ihφ.some.andI ihψ.some⟩
  | andEL _ ih => exact ⟨ih.some.andEL⟩
  | andER _ ih => exact ⟨ih.some.andER⟩
  | orIL _ ih => exact ⟨ih.some.orIL⟩
  | orIR _ ih => exact ⟨ih.some.orIR⟩
  | orE _ _ _ ih ihl ihr => exact ⟨ih.some.orE ihl.some ihr.some⟩
  | impI _ ih => exact ⟨ih.some.impI⟩
  | impE _ _ ihimp ihφ => exact ⟨ihimp.some.impE ihφ.some⟩
  | notI _ ih => exact ⟨ih.some.notI⟩
  | notE _ _ ihnot ihφ => exact ⟨ihnot.some.notE ihφ.some⟩
  | allI _ ih => exact ⟨ih.some.allI⟩
  | allE t _ ih => exact ⟨ih.some.allE t⟩
  | exI t _ ih => exact ⟨ih.some.exI t⟩
  | exE _ _ ihex ihbody => exact ⟨ihex.some.exE ihbody.some⟩
  | eqRefl t => exact supportedStageDerivation_eqRefl t
  | eqSymm _ ih => exact ⟨ih.some.eqSymm⟩
  | eqTrans _ _ ihtu ihuv => exact ⟨ihtu.some.eqTrans ihuv.some⟩
  | eqPropI _ _ ihpq ihqp => exact ⟨ihpq.some.eqPropI ihqp.some⟩
  | eqPropEL _ ih => exact ⟨ih.some.eqPropEL⟩
  | eqPropER _ ih => exact ⟨ih.some.eqPropER⟩
  | eqApp t _ ih => exact ⟨ih.some.eqApp t⟩
  | eqAppArg f _ ih => exact ⟨ih.some.eqAppArg f⟩
  | eqLam _ ih => exact ⟨ih.some.eqLam⟩
  | funExt _ ih => exact ⟨ih.some.funExt⟩
  | beta t u => exact supportedStageDerivation_beta t u
  | eta f => exact supportedStageDerivation_eta f

end HenkinConstInfinity

end Mettapedia.Logic.HOL
