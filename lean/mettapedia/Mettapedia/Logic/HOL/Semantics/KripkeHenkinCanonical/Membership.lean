import Mettapedia.Logic.HOL.Semantics.KripkeHenkin

/-!
# Canonical membership bridges

Same-world membership clauses for presented and supported presented canonical
worlds.  These lemmas are the local algebraic bridge between closed-theory
membership and the formulas later read by the Kripke-Henkin packaging layer.
-/

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

open Mettapedia.Logic.HOL.WithParams

namespace KripkeHenkin
/-! ## Canonical membership bridges

These same-world clauses are the part of the canonical truth lemma that does not
need a Kripke successor construction.  The implication, negation, and universal
converses are intentionally left to the presented-world successor lemmas.
-/

namespace CanonicalMembership

open ClosedTheorySet

variable {W : ClosedTheorySet.PresentedIntuitionisticWorld Const}

theorem top_mem (W : ClosedTheorySet.PresentedIntuitionisticWorld Const) :
    (.top : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_top (Const := WithParams Const) W.carrier

theorem bot_not_mem (W : ClosedTheorySet.PresentedIntuitionisticWorld Const) :
    (.bot : ClosedFormula (WithParams Const)) ∉ W.carrier :=
  ClosedTheorySet.IntuitionisticWorld.bot_not_mem (W := W.toIntuitionisticWorld)

theorem and_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : φ ∈ W.carrier) (hψ : ψ ∈ W.carrier) :
    (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_intro (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφ)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)

theorem and_left_mem {φ ψ : ClosedFormula (WithParams Const)}
    (h : (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    φ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_left (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem and_right_mem {φ ψ : ClosedFormula (WithParams Const)}
    (h : (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_right (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem and_iff {φ ψ : ClosedFormula (WithParams Const)} :
    (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      φ ∈ W.carrier ∧ ψ ∈ W.carrier := by
  constructor
  · intro h
    exact ⟨and_left_mem (W := W) h, and_right_mem (W := W) h⟩
  · intro h
    exact and_mem (W := W) h.1 h.2

theorem or_left_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : φ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_or_intro_left (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφ)

theorem or_right_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hψ : ψ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_or_intro_right (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)

theorem or_iff {φ ψ : ClosedFormula (WithParams Const)} :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      φ ∈ W.carrier ∨ ψ ∈ W.carrier := by
  constructor
  · intro h
    exact W.prime_or h
  · intro h
    rcases h with hφ | hψ
    · exact or_left_mem (W := W) hφ
    · exact or_right_mem (W := W) hψ

theorem all_elim_mem {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (t : ClosedTerm (WithParams Const) σ)
    (h : (.all φ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    instantiate (Base := Base) t φ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_all_elim (Const := WithParams Const) t
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem ex_intro_mem {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (t : ClosedTerm (WithParams Const) σ)
    (h : instantiate (Base := Base) t φ ∈ W.carrier) :
    (.ex φ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_ex_intro (Const := WithParams Const) t
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem ex_iff {σ : Ty Base} {φ : Formula (WithParams Const) [σ]} :
    (.ex φ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈ W.carrier := by
  constructor
  · exact W.exists_witness
  · rintro ⟨t, ht⟩
    exact ex_intro_mem (W := W) t ht

theorem imp_mp_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hφ : φ ∈ W.carrier) :
    ψ ∈ W.carrier :=
  ClosedTheorySet.IntuitionisticWorld.mp (W := W.toIntuitionisticWorld) hImp hφ

theorem provable_eq_prop_intro (T : ClosedTheorySet (WithParams Const))
    {p q : ClosedFormula (WithParams Const)}
    (hpq : ClosedTheorySet.Provable (Const := WithParams Const) T (.imp p q))
    (hqp : ClosedTheorySet.Provable (Const := WithParams Const) T (.imp q p)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.eq p q) := by
  rcases hpq with ⟨Γ₁, hΓ₁, d₁⟩
  rcases hqp with ⟨Γ₂, hΓ₂, d₂⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with hξ | hξ
    · exact hΓ₁ ξ hξ
    · exact hΓ₂ ξ hξ
  · exact ExtDerivation.eqPropI
      (ExtDerivation.mono
        (by intro ξ hξ; exact List.mem_append.mpr (.inl hξ)) d₁)
      (ExtDerivation.mono
        (by intro ξ hξ; exact List.mem_append.mpr (.inr hξ)) d₂)

theorem provable_eq_prop_elim_left (T : ClosedTheorySet (WithParams Const))
    {p q : ClosedFormula (WithParams Const)}
    (hpq : ClosedTheorySet.Provable (Const := WithParams Const) T (.eq p q)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp p q) := by
  rcases hpq with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqPropEL d⟩

theorem provable_eq_prop_elim_right (T : ClosedTheorySet (WithParams Const))
    {p q : ClosedFormula (WithParams Const)}
    (hpq : ClosedTheorySet.Provable (Const := WithParams Const) T (.eq p q)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T (.imp q p) := by
  rcases hpq with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, ExtDerivation.eqPropER d⟩

theorem provable_eq_beta (T : ClosedTheorySet (WithParams Const))
    {σ τ : Ty Base} (t : ClosedTerm (WithParams Const) σ)
    (u : Term (WithParams Const) [σ] τ) :
    ClosedTheorySet.Provable (Const := WithParams Const) T
      (.eq (.app (.lam u) t) (instantiate (Base := Base) t u)) := by
  refine ⟨[], ?_, ?_⟩
  · intro ξ hξ
    cases hξ
  · exact ExtDerivation.beta t u

theorem provable_eq_eta (T : ClosedTheorySet (WithParams Const))
    {σ τ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ τ)) :
    ClosedTheorySet.Provable (Const := WithParams Const) T
      (.eq (.lam (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f)
        (.var .vz))) f) := by
  refine ⟨[], ?_, ?_⟩
  · intro ξ hξ
    cases hξ
  · exact ExtDerivation.eta f

theorem eq_refl_mem {τ : Ty Base} (t : ClosedTerm (WithParams Const) τ) :
    (.eq t t : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_refl (Const := WithParams Const) W.carrier t

theorem eq_symm_mem {τ : Ty Base} {s t : ClosedTerm (WithParams Const) τ}
    (h : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq t s : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_symm
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem eq_trans_mem {τ : Ty Base} {r s t : ClosedTerm (WithParams Const) τ}
    (hrs : (.eq r s : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hst : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq r t : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_trans
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hrs)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hst)

theorem eq_app_congr_mem {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    {s t : ClosedTerm (WithParams Const) σ}
    (hfg : (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hst : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq (.app f s) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  have hfgs : (.eq (.app f s) (.app g s) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    apply W.closed
    exact ClosedTheorySet.provable_eq_app (Const := WithParams Const) s
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hfg)
  have hgst : (.eq (.app g s) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    apply W.closed
    exact ClosedTheorySet.provable_eq_appArg (Const := WithParams Const) g
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hst)
  exact eq_trans_mem (W := W) hfgs hgst

theorem eq_funext_mem_of_fresh_param {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    {m k : Nat} (hm : W.level ≤ m)
    (hBody : NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
      (.eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
        (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
        : Formula (WithParams Const) [σ]))
    (hInst :
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) ∈
        W.carrier) :
    (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  let body : Formula (WithParams Const) [σ] :=
    .eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
      (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
  have hInstRaw0 : ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) := by
    change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) at hInst
    exact hInst
  have hInstRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (instantiate (Base := Base) (.const (param σ (Nat.pair m k))) body) := by
    convert hInstRaw0 using 1
    simp [body, instantiate, subst, Subst.single, weaken]
    constructor
    · exact instantiate_weaken (Base := Base) (Const := WithParams Const)
        (t := (.const (param σ (Nat.pair m k)) : ClosedTerm (WithParams Const) σ)) (u := f)
    · exact instantiate_weaken (Base := Base) (Const := WithParams Const)
        (t := (.const (param σ (Nat.pair m k)) : ClosedTerm (WithParams Const) σ)) (u := g)
  have hAllRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.all body) :=
    ClosedTheorySet.provable_all_intro_fresh
      (Const := WithParams Const)
      (T := W.raw)
      (c := param σ (Nat.pair m k))
      (by
        intro ψ hψ
        exact W.raw_avoids_future ψ hψ σ m k hm)
      hBody
      hInstRaw
  have hAllMem : (.all body : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.all body)
    exact hAllRaw
  apply W.closed
  exact ClosedTheorySet.provable_eq_funext
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hAllMem)

theorem eq_funext_mem {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    (hpoint :
      ∀ t : ClosedTerm (WithParams Const) σ,
        (.eq (.app f t) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  let body : Formula (WithParams Const) [σ] :=
    .eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
      (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
  let m : Nat := W.level + maxParam body + 1
  have hm : W.level ≤ m := by
    omega
  have hBody : NoConstOccurrence (param σ (Nat.pair m 0) : WithParams Const σ) body := by
    have hMax : maxParam body ≤ m := by
      omega
    exact noConstOccurrence_param_of_ge (Nat.pair m 0) body
      (Nat.le_trans hMax (Nat.left_le_pair m 0))
  exact eq_funext_mem_of_fresh_param (W := W) (m := m) (k := 0) hm hBody
    (hpoint (.const (param σ (Nat.pair m 0))))

theorem eq_prop_intro_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.imp p q : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hqp : (.imp q p : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact provable_eq_prop_intro (W.carrier)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hqp)

theorem eq_prop_elim_left_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.imp p q : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact provable_eq_prop_elim_left W.carrier
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)

theorem eq_prop_elim_right_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.imp q p : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact provable_eq_prop_elim_right W.carrier
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)

theorem eq_beta_mem {σ τ : Ty Base}
    (t : ClosedTerm (WithParams Const) σ) (u : Term (WithParams Const) [σ] τ) :
    (.eq (.app (.lam u) t) (instantiate (Base := Base) t u)
      : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact provable_eq_beta W.carrier t u

theorem eq_eta_mem {σ τ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ τ)) :
    (.eq (.lam (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f)
        (.var .vz))) f : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact provable_eq_eta W.carrier f

end CanonicalMembership

/-! ## Supported canonical membership bridges -/

namespace SupportedCanonicalMembership

open ClosedTheorySet

variable {W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const}

theorem top_mem (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    (.top : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_top (Const := WithParams Const) W.carrier

theorem bot_not_mem (W : ClosedTheorySet.SupportedPresentedIntuitionisticWorld Const) :
    (.bot : ClosedFormula (WithParams Const)) ∉ W.carrier := by
  intro hbot
  exact W.consistent
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hbot)

theorem and_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : φ ∈ W.carrier) (hψ : ψ ∈ W.carrier) :
    (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_intro (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφ)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)

theorem and_left_mem {φ ψ : ClosedFormula (WithParams Const)}
    (h : (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    φ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_left (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem and_right_mem {φ ψ : ClosedFormula (WithParams Const)}
    (h : (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_and_right (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem and_iff {φ ψ : ClosedFormula (WithParams Const)} :
    (.and φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      φ ∈ W.carrier ∧ ψ ∈ W.carrier := by
  constructor
  · intro h
    exact ⟨and_left_mem (W := W) h, and_right_mem (W := W) h⟩
  · intro h
    exact and_mem (W := W) h.1 h.2

theorem or_left_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hφ : φ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_or_intro_left (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφ)

theorem or_right_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hψ : ψ ∈ W.carrier) :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_or_intro_right (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hψ)

theorem or_iff {φ ψ : ClosedFormula (WithParams Const)}
    (hPair :
      ClosedTheorySet.FormulaPairAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (φ, ψ)) :
    (.or φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      φ ∈ W.carrier ∨ ψ ∈ W.carrier := by
  constructor
  · intro h
    exact W.supported_prime_or hPair h
  · intro h
    rcases h with hφ | hψ
    · exact or_left_mem (W := W) hφ
    · exact or_right_mem (W := W) hψ

theorem all_elim_mem {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (t : ClosedTerm (WithParams Const) σ)
    (h : (.all φ : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    instantiate (Base := Base) t φ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_all_elim (Const := WithParams Const) t
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem ex_intro_mem {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (t : ClosedTerm (WithParams Const) σ)
    (h : instantiate (Base := Base) t φ ∈ W.carrier) :
    (.ex φ : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_ex_intro (Const := WithParams Const) t
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem ex_iff {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hBody :
      ClosedTheorySet.BodyAvoidsParamLayersFromAt
        (Base := Base) (Const := Const) W.level (⟨σ, φ⟩ : Body Const)) :
    (.ex φ : ClosedFormula (WithParams Const)) ∈ W.carrier ↔
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈ W.carrier := by
  constructor
  · exact W.supported_exists_witness hBody
  · rintro ⟨t, ht⟩
    exact ex_intro_mem (W := W) t ht

theorem imp_mp_mem {φ ψ : ClosedFormula (WithParams Const)}
    (hImp : (.imp φ ψ : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hφ : φ ∈ W.carrier) :
    ψ ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_mp (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hImp)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hφ)

theorem eq_refl_mem {τ : Ty Base} (t : ClosedTerm (WithParams Const) τ) :
    (.eq t t : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_refl (Const := WithParams Const) W.carrier t

theorem eq_symm_mem {τ : Ty Base} {s t : ClosedTerm (WithParams Const) τ}
    (h : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq t s : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_symm
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) h)

theorem eq_trans_mem {τ : Ty Base} {r s t : ClosedTerm (WithParams Const) τ}
    (hrs : (.eq r s : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hst : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq r t : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact ClosedTheorySet.provable_eq_trans
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hrs)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hst)

theorem eq_app_congr_mem {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    {s t : ClosedTerm (WithParams Const) σ}
    (hfg : (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hst : (.eq s t : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq (.app f s) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  have hfgs : (.eq (.app f s) (.app g s) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    apply W.closed
    exact ClosedTheorySet.provable_eq_app (Const := WithParams Const) s
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hfg)
  have hgst : (.eq (.app g s) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    apply W.closed
    exact ClosedTheorySet.provable_eq_appArg (Const := WithParams Const) g
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hst)
  exact eq_trans_mem (W := W) hfgs hgst

theorem eq_funext_mem_of_fresh_param {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    {m k : Nat} (hm : W.level ≤ m)
    (hBody : NoConstOccurrence (param σ (Nat.pair m k) : WithParams Const σ)
      (.eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
        (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
        : Formula (WithParams Const) [σ]))
    (hInst :
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) ∈
        W.carrier) :
    (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  let body : Formula (WithParams Const) [σ] :=
    .eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
      (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
  have hInstRaw0 : ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) := by
    change ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (.eq (.app f (.const (param σ (Nat.pair m k))))
        (.app g (.const (param σ (Nat.pair m k)))) : ClosedFormula (WithParams Const)) at hInst
    exact hInst
  have hInstRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw
      (instantiate (Base := Base) (.const (param σ (Nat.pair m k))) body) := by
    convert hInstRaw0 using 1
    simp [body, instantiate, subst, Subst.single, weaken]
    constructor
    · exact instantiate_weaken (Base := Base) (Const := WithParams Const)
        (t := (.const (param σ (Nat.pair m k)) : ClosedTerm (WithParams Const) σ)) (u := f)
    · exact instantiate_weaken (Base := Base) (Const := WithParams Const)
        (t := (.const (param σ (Nat.pair m k)) : ClosedTerm (WithParams Const) σ)) (u := g)
  have hAllRaw : ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.all body) :=
    ClosedTheorySet.provable_all_intro_fresh
      (Const := WithParams Const)
      (T := W.raw)
      (c := param σ (Nat.pair m k))
      (by
        intro ψ hψ
        exact W.raw_avoids_future ψ hψ σ m k hm)
      hBody
      hInstRaw
  have hAllMem : (.all body : ClosedFormula (WithParams Const)) ∈ W.carrier := by
    change ClosedTheorySet.Provable (Const := WithParams Const) W.raw (.all body)
    exact hAllRaw
  apply W.closed
  exact ClosedTheorySet.provable_eq_funext
    (Const := WithParams Const)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hAllMem)

theorem eq_funext_mem {σ τ : Ty Base}
    {f g : ClosedTerm (WithParams Const) (σ ⇒ τ)}
    (hpoint :
      ∀ t : ClosedTerm (WithParams Const) σ,
        (.eq (.app f t) (.app g t) : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq f g : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  let body : Formula (WithParams Const) [σ] :=
    .eq (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f) (.var .vz))
      (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) g) (.var .vz))
  let m : Nat := W.level + maxParam body + 1
  have hm : W.level ≤ m := by
    omega
  have hBody : NoConstOccurrence (param σ (Nat.pair m 0) : WithParams Const σ) body := by
    have hMax : maxParam body ≤ m := by
      omega
    exact noConstOccurrence_param_of_ge (Nat.pair m 0) body
      (Nat.le_trans hMax (Nat.left_le_pair m 0))
  exact eq_funext_mem_of_fresh_param (W := W) (m := m) (k := 0) hm hBody
    (hpoint (.const (param σ (Nat.pair m 0))))

theorem eq_prop_intro_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.imp p q : ClosedFormula (WithParams Const)) ∈ W.carrier)
    (hqp : (.imp q p : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact CanonicalMembership.provable_eq_prop_intro (W.carrier)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hqp)

theorem eq_prop_elim_left_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.imp p q : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact CanonicalMembership.provable_eq_prop_elim_left W.carrier
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)

theorem eq_prop_elim_right_mem {p q : ClosedFormula (WithParams Const)}
    (hpq : (.eq p q : ClosedFormula (WithParams Const)) ∈ W.carrier) :
    (.imp q p : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact CanonicalMembership.provable_eq_prop_elim_right W.carrier
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hpq)

theorem eq_beta_mem {σ τ : Ty Base}
    (t : ClosedTerm (WithParams Const) σ) (u : Term (WithParams Const) [σ] τ) :
    (.eq (.app (.lam u) t) (instantiate (Base := Base) t u)
      : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact CanonicalMembership.provable_eq_beta W.carrier t u

theorem eq_eta_mem {σ τ : Ty Base} (f : ClosedTerm (WithParams Const) (σ ⇒ τ)) :
    (.eq (.lam (.app (weaken (Base := Base) (Const := WithParams Const) (σ := σ) f)
        (.var .vz))) f : ClosedFormula (WithParams Const)) ∈ W.carrier := by
  apply W.closed
  exact CanonicalMembership.provable_eq_eta W.carrier f

end SupportedCanonicalMembership

end KripkeHenkin

end Mettapedia.Logic.HOL
