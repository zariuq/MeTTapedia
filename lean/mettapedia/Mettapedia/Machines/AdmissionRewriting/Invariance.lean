import Mettapedia.Machines.AdmissionRewriting.Dialects
import Mettapedia.Machines.AdmissionModuloEquations

/-!
# Admission on normal forms: invariant under the equations, faithful to the original

The rewrite system of `Syntax`, its normalizer of `Normalizer`, and a ready dialect of
`Semantics` together form an `AdmissionModuloEquations.Language`: the equations are the
conversion of the rules, the observation of a term is its trace in every environment
that respects the facts, and the normalizer is canonical.  Every theorem of
`AdmissionModuloEquations` therefore holds for the admission fragment:

* `admission_invariant`: a tier offered normal forms admits a term exactly when it admits
  every term the rules equate to it: its boundary is a union of conversion classes;
* `normalized_answers`: whatever it answers is the original term's trace: the same
  answers in the same order with the same multiplicities, and the same effects;
* `normalized_admits_more`: if admission is closed under the normalizer, the normalized
  tier admits everything the spelled tier admits; `normalized_admits_all`: a tier whose
  only refusals are rewritable spellings admits every program once offered normal forms;
* `fixture_law`, `fixture_law_bag`, `fixture_law_effects`: on any list of fixtures, the
  normalized program and the original answer alike, as traces, as answer bags, and as
  effect sequences;
* `metered_normalizer_observable`: under a fuel meter the normalizer is observable, so a
  metered run must be given the original spelling.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting

open AdmissionModuloEquations

/-- Environments that respect the facts. -/
abbrev Env (Γ : Facts) := {ρ : List Val // Sat Γ ρ}

/-- The admission fragment on a ready dialect, as a language with an equational theory
and a normalizer. -/
def language (D : Dialect) (hD : Ready D) (Γ : Facts) : Language Tm (Env Γ → Trace) where
  eval t := fun ρ => eval D t ρ.1
  equiv := Relation.EqvGen (Step true Γ)
  equiv_eval _ _ h := funext fun ρ => conv_sound hD h ρ.1 ρ.2
  norm := N Γ
  norm_equiv t := conv_N Γ t

/-- The normalizer is canonical for the rules' equations. -/
theorem language_canonical (D : Dialect) (hD : Ready D) (Γ : Facts) :
    Canonical (language D hD Γ) := fun _ _ h => canonical h

section Route

variable {D : Dialect} {hD : Ready D} {Γ : Facts}

/-- A tier offered normal forms admits a term exactly when it admits every term the
rules equate to it. -/
theorem admission_invariant (R : Route (language D hD Γ)) {p q : Tm}
    (h : Relation.EqvGen (Step true Γ) p q) :
    (R.normalized p).isSome = (R.normalized q).isSome :=
  normalized_admitted_closed R (language_canonical D hD Γ) p q h

/-- Its answers on equal terms are equal. -/
theorem normalized_respects_conv (R : Route (language D hD Γ)) {p q : Tm}
    (h : Relation.EqvGen (Step true Γ) p q) : R.normalized p = R.normalized q :=
  normalized_respects R (language_canonical D hD Γ) p q h

/-- What the tier offered normal forms answers is the original term's trace. -/
theorem normalized_answers (R : Route (language D hD Γ)) (p : Tm) (o : Env Γ → Trace)
    (h : R.normalized p = some o) : ∀ ρ : Env Γ, o ρ = AdmissionRewriting.eval D p ρ.1 := by
  have := normalized_sound R p o h
  intro ρ
  rw [this]
  rfl

end Route

/-- A tier that answers exactly the terms an admission test accepts, correctly. -/
def tier (D : Dialect) (hD : Ready D) (Γ : Facts) (adm : Tm → Bool) : Route (language D hD Γ) where
  fast t := if adm t then some (fun ρ => eval D t ρ.1) else none
  sound p o h := by
    by_cases ha : adm p
    · simp only [ha, if_true, Option.some.injEq] at h; exact h.symm
    · simp [ha] at h

theorem tier_normalized_isSome (D : Dialect) (hD : Ready D) (Γ : Facts) (adm : Tm → Bool)
    (p : Tm) : ((tier D hD Γ adm).normalized p).isSome = adm (N Γ p) := by
  simp only [Route.normalized, tier, language]
  split <;> simp_all

/-- If admission is closed under the normalizer, the normalized tier admits all that the
spelled tier admits. -/
theorem normalized_admits_more (D : Dialect) (hD : Ready D) (Γ : Facts) (adm : Tm → Bool)
    (hclosed : ∀ t, adm t = true → adm (N Γ t) = true) (p : Tm) (h : adm p = true) :
    ((tier D hD Γ adm).normalized p).isSome = true := by
  rw [tier_normalized_isSome]; exact hclosed p h

/-- A tier whose only refusals are spellings some rule rewrites (it admits every
irreducible term) admits every program once offered normal forms: the spelling cliffs
close. -/
theorem normalized_admits_all (D : Dialect) (hD : Ready D) (Γ : Facts) (adm : Tm → Bool)
    (hirr : ∀ t, (∀ t', ¬ Step true Γ t t') → adm t = true) (p : Tm) :
    ((tier D hD Γ adm).normalized p).isSome = true := by
  rw [tier_normalized_isSome]
  exact hirr _ (N_irreducible Γ p)

/-- The answers of a trace. -/
def answers : Trace → List Val
  | [] => []
  | .ans v :: t => v :: answers t
  | .eff _ :: t => answers t

/-- The effects of a trace. -/
def effects : Trace → List ℕ
  | [] => []
  | .ans _ :: t => effects t
  | .eff n :: t => n :: effects t

/-- The fixture law: each normalized fixture answers as the fixture does. -/
theorem fixture_law {D : Dialect} (hD : Ready D) (Γ : Facts) (fixtures : List Tm)
    (ρ : List Val) (hρ : Sat Γ ρ) : ∀ p ∈ fixtures, eval D (N Γ p) ρ = eval D p ρ :=
  fun p _ => N_sound hD Γ p ρ hρ

/-- The fixture law on answer bags. -/
theorem fixture_law_bag {D : Dialect} (hD : Ready D) (Γ : Facts) (fixtures : List Tm)
    (ρ : List Val) (hρ : Sat Γ ρ) :
    ∀ p ∈ fixtures, (answers (eval D (N Γ p) ρ) : Multiset Val) = answers (eval D p ρ) :=
  fun p hp => by rw [fixture_law hD Γ fixtures ρ hρ p hp]

/-- The fixture law on effects. -/
theorem fixture_law_effects {D : Dialect} (hD : Ready D) (Γ : Facts) (fixtures : List Tm)
    (ρ : List Val) (hρ : Sat Γ ρ) :
    ∀ p ∈ fixtures, effects (eval D (N Γ p) ρ) = effects (eval D p ρ) :=
  fun p hp => by rw [fixture_law hD Γ fixtures ρ hρ p hp]

/-- The closed programs of PeTTa: the law in the dialect the compiled tier runs. -/
theorem petta_fixture_law (fixtures : List Tm) :
    ∀ p ∈ fixtures, eval Dialects.petta (N (fun _ => false) p) [] = eval Dialects.petta p [] :=
  fixture_law Dialects.petta_ready _ fixtures [] (fun _ h => by simp at h)

/-- Under a fuel meter the normalizer is observable: `(id 5)` normalizes to `5`, which
takes one step fewer. -/
theorem metered_normalizer_observable :
    eval Dialects.metered (N (fun _ => false) (.call .id [.lit (.int 5)])) [] ≠
      eval Dialects.metered (.call .id [.lit (.int 5)]) [] := by
  have hN : N (fun _ => false) (.call .id [.lit (.int 5)]) = .lit (.int 5) := rfl
  rw [hN]
  exact (Dialects.metered_id_differs).symm

end Mettapedia.Machines.AdmissionRewriting
