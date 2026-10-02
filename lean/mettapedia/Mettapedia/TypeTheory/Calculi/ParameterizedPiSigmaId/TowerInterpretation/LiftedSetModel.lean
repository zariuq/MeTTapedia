import Mettapedia.Logic.HOL.Embedding.ZFSetLiftedTraceProducts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.Soundness

/-!
# The set model carried up one universe

Evaluation of an annotated term commutes with the universe lift. A context is
satisfied in the lifted reading exactly by the lifts of the environments that
satisfy it below. A universe model, a statement that holds, and a set model of
a package all carry from a head valuation to the pointwise lift of that
valuation. The set of every lower set, read one universe up, is not the value
of any term at a lifted environment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseLift
open ZFSetLiftedTraceProducts
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceApp_graph_beta)
open ZFSetReplayInterpretation (UniverseModel)

universe u

variable {Head : Type}

noncomputable section

variable (heads : Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})

theorem extend_lift {n : Nat} (ρ : Env.{u} n) (x : ZFSet.{u}) :
    extend (lift ∘ ρ) (lift x) = lift ∘ extend ρ x := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i
  · rfl
  · rfl

theorem env_eq_extend.{v} {n : Nat} (ρ : Fin (n + 1) → ZFSet.{v}) :
    ρ = extend.{v} (ρ ∘ Fin.succ) (ρ 0) := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i
  · rfl
  · rfl

/-- The value of a term at a lifted environment is the lift of its value. -/
theorem ev_lift {n : Nat} (t : CTm Head n) (ρ : Env.{u} n) :
    ev (lift ∘ heads) (lift ∘ consts) t (lift ∘ ρ) = lift (ev heads consts t ρ) := by
  induction t with
  | var _ => rfl
  | const _ => rfl
  | head _ => rfl
  | pi A B ihA ihB =>
      simp only [ev, ihA]
      rw [← lift_tracePiSet (ev heads consts A ρ) (fun x => ev heads consts B (extend ρ x))
          (fun y => ev (lift ∘ heads) (lift ∘ consts) B (extend (lift ∘ ρ) y))
          (fun x _ => by rw [extend_lift, ihB])]
  | sigma A B ihA ihB =>
      simp only [ev, ihA]
      rw [← lift_sigmaSet (ev heads consts A ρ) (fun x => ev heads consts B (extend ρ x))
          (fun y => ev (lift ∘ heads) (lift ∘ consts) B (extend (lift ∘ ρ) y))
          (fun x _ => by rw [extend_lift, ihB])]
  | id _ a b _ iha ihb =>
      simp only [ev, iha, ihb]
      rw [← lift_truthCode, truthCode_iff lift_injective.eq_iff]
  | lam A body ihA ihBody =>
      simp only [ev, ihA]
      rw [lift_traceLam,
        lift_graph (ev heads consts A ρ) (fun x => ev heads consts body (extend ρ x))
          (fun y => ev (lift ∘ heads) (lift ∘ consts) body (extend (lift ∘ ρ) y))
          (fun x _ => by rw [extend_lift, ihBody])]
  | app f a ihf iha =>
      simp only [ev, ihf, iha]
      rw [← lift_traceApp]
  | pair a b iha ihb =>
      simp only [ev, iha, ihb]
      rw [← lift_pair]
  | fst p ih =>
      simp only [ev, ih]
      rw [← lift_first]
  | snd p ih =>
      simp only [ev, ih]
      rw [← lift_second]
  | refl _ _ =>
      simp only [ev]
      rw [lift_empty]

/-- Below, the identity on `A` applied to a member denotes that member. -/
theorem identity_app_below {n : Nat} (A a : CTm Head n) (ρ : Env.{u} n)
    (member : ev heads consts a ρ ∈ ev heads consts A ρ) :
    ev heads consts (.app (.lam A (.var 0)) a) ρ = ev heads consts a ρ := by
  simp only [ev]
  exact (traceApp_graph_beta (fun x => (extend ρ x) 0) member).trans (extend_zero ρ _)

/-- At lifted heads, the identity on `A` applied to a member denotes the lift of that member. -/
theorem identity_app_lift {n : Nat} (A a : CTm Head n) (ρ : Env.{u} n)
    (member : ev heads consts a ρ ∈ ev heads consts A ρ) :
    ev (lift ∘ heads) (lift ∘ consts) (.app (.lam A (.var 0)) a) (lift ∘ ρ) =
      lift (ev heads consts a ρ) := by
  rw [ev_lift, identity_app_below heads consts A a ρ member]

theorem sat_lift_of_sat {n : Nat} {Γ : CCtx Head n} {ρ : Env.{u} n}
    (sat : Sat heads consts Γ ρ) :
    Sat (lift ∘ heads) (lift ∘ consts) Γ (lift ∘ ρ) := by
  intro i
  rw [ev_lift]
  exact lift_mem_lift.mpr (sat i)

theorem sat_lift_down {n : Nat} (Γ : CCtx Head n) (ρ' : Env.{u + 1} n)
    (sat : Sat (lift ∘ heads) (lift ∘ consts) Γ ρ') :
    ∃ ρ : Env.{u} n, ρ' = lift ∘ ρ ∧ Sat heads consts Γ ρ := by
  induction Γ with
  | nil =>
      refine ⟨Fin.elim0, ?_, sat_nil heads consts Fin.elim0⟩
      funext i
      exact i.elim0
  | snoc Γ A ih =>
      have eqEnv : ρ' = extend (ρ' ∘ Fin.succ) (ρ' 0) := env_eq_extend ρ'
      rw [eqEnv] at sat
      obtain ⟨satTail, hx⟩ := (sat_snoc (lift ∘ heads) (lift ∘ consts)).mp sat
      obtain ⟨ρ, htail, satρ⟩ := ih (ρ' ∘ Fin.succ) satTail
      rw [htail, ev_lift] at hx
      obtain ⟨x, hxA, hx0⟩ := mem_lift.mp hx
      refine ⟨extend ρ x, ?_, (sat_snoc heads consts).mpr ⟨satρ, hxA⟩⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hx0.symm
      · exact congrFun htail j

/-- An environment satisfies a context in the lifted reading exactly when it is
the lift of an environment that satisfies the context below. -/
theorem sat_lift_iff {n : Nat} (Γ : CCtx Head n) (ρ' : Env.{u + 1} n) :
    Sat (lift ∘ heads) (lift ∘ consts) Γ ρ' ↔
      ∃ ρ : Env.{u} n, ρ' = lift ∘ ρ ∧ Sat heads consts Γ ρ := by
  constructor
  · exact sat_lift_down heads consts Γ ρ'
  · rintro ⟨ρ, rfl, sat⟩
    exact sat_lift_of_sat heads consts sat

theorem holds_lift_iff (s : CStatement Head) :
    Holds heads consts s ↔ Holds (lift ∘ heads) (lift ∘ consts) s := by
  cases s with
  | typing Γ t A =>
      constructor
      · intro held ρ' sat
        obtain ⟨ρ, rfl, satρ⟩ := sat_lift_down heads consts Γ ρ' sat
        rw [ev_lift, ev_lift]
        exact lift_mem_lift.mpr (held ρ satρ)
      · intro held ρ sat
        have hmem := held (lift ∘ ρ) (sat_lift_of_sat heads consts sat)
        rw [ev_lift, ev_lift] at hmem
        exact lift_mem_lift.mp hmem
  | equality Γ a b A =>
      constructor
      · intro held ρ' sat
        obtain ⟨ρ, rfl, satρ⟩ := sat_lift_down heads consts Γ ρ' sat
        obtain ⟨heq, hmem⟩ := held ρ satρ
        rw [ev_lift, ev_lift, ev_lift]
        exact ⟨congrArg lift heq, lift_mem_lift.mpr hmem⟩
      · intro held ρ sat
        obtain ⟨heq, hmem⟩ := held (lift ∘ ρ) (sat_lift_of_sat heads consts sat)
        rw [ev_lift (t := a), ev_lift (t := b)] at heq
        rw [ev_lift (t := a), ev_lift (t := A)] at hmem
        exact ⟨lift_injective heq, lift_mem_lift.mp hmem⟩
  | sub Γ A B =>
      constructor
      · intro held ρ' sat
        obtain ⟨ρ, rfl, satρ⟩ := sat_lift_down heads consts Γ ρ' sat
        rw [ev_lift, ev_lift]
        exact lift_subset_lift.mpr (held ρ satρ)
      · intro held ρ sat
        have hsub := held (lift ∘ ρ) (sat_lift_of_sat heads consts sat)
        rw [ev_lift, ev_lift] at hsub
        exact lift_subset_lift.mp hsub

/-- Every value at lifted heads, lifted constants and a lifted environment is a
lift, so the set of all lower sets is the value of no such term. -/
theorem ev_lifted_mem_carrierCode {n : Nat} (t : CTm Head n) (ρ : Env.{u} n) :
    ev (lift ∘ heads) (lift ∘ consts) t (lift ∘ ρ) ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨ev heads consts t ρ, (ev_lift heads consts t ρ).symm⟩

theorem ev_lifted_ne_carrierCode {n : Nat} (t : CTm Head n) (ρ : Env.{u} n) :
    ev (lift ∘ heads) (lift ∘ consts) t (lift ∘ ρ) ≠ carrierCode.{u} := by
  intro equal
  exact carrier_not_member (equal ▸ ev_lifted_mem_carrierCode heads consts t ρ)

variable {R : Rules Head}

theorem universeModel_lift (model : UniverseModel R heads) :
    UniverseModel R (lift ∘ heads) where
  headTyping_mem := by
    intro _ _ typed
    exact lift_mem_lift.mpr (model.headTyping_mem typed)
  cumulative_subset := by
    intro _ _ cumulative
    exact lift_subset_lift.mpr (model.cumulative_subset cumulative)
  pi_mem := by
    intro _ bodyLevel _ joined A hA B fibre
    obtain ⟨a, ha, rfl⟩ := mem_lift.mp hA
    let b : ZFSet.{u} → ZFSet.{u} := fun x => lowerValue (B (lift x))
    have agree : ∀ x ∈ a, B (lift x) = lift (b x) := by
      intro x hx
      obtain ⟨z, _, hz⟩ := mem_lift.mp (fibre (lift x) (lift_mem_lift.mpr hx))
      exact (lift_lowerValue (mem_carrierCode.mpr ⟨z, hz⟩)).symm
    have hb : ∀ x ∈ a, b x ∈ heads bodyLevel := by
      intro x hx
      apply lift_mem_lift.mp
      rw [← agree x hx]
      exact fibre (lift x) (lift_mem_lift.mpr hx)
    rw [← lift_tracePiSet a b B agree]
    exact lift_mem_lift.mpr (model.pi_mem joined ha b hb)
  sigma_mem := by
    intro _ bodyLevel _ joined A hA B fibre
    obtain ⟨a, ha, rfl⟩ := mem_lift.mp hA
    let b : ZFSet.{u} → ZFSet.{u} := fun x => lowerValue (B (lift x))
    have agree : ∀ x ∈ a, B (lift x) = lift (b x) := by
      intro x hx
      obtain ⟨z, _, hz⟩ := mem_lift.mp (fibre (lift x) (lift_mem_lift.mpr hx))
      exact (lift_lowerValue (mem_carrierCode.mpr ⟨z, hz⟩)).symm
    have hb : ∀ x ∈ a, b x ∈ heads bodyLevel := by
      intro x hx
      apply lift_mem_lift.mp
      rw [← agree x hx]
      exact fibre (lift x) (lift_mem_lift.mpr hx)
    rw [← lift_sigmaSet a b B agree]
    exact lift_mem_lift.mpr (model.sigma_mem joined ha b hb)
  identity_mem := by
    intro _ isUniverse P
    rw [← lift_truthCode]
    exact lift_mem_lift.mpr (model.identity_mem isUniverse P)

variable {P : ChurchRules R}

theorem setModel_lift (model : SetModel heads consts P) :
    SetModel (lift ∘ heads) (lift ∘ consts) P where
  universes := universeModel_lift heads model.universes
  headEq := by
    intro _ _ equal
    exact congrArg lift (model.headEq equal)
  constants := by
    intro c T known
    have henv : lift ∘ (Fin.elim0 : Env.{u} 0) = (Fin.elim0 : Env.{u + 1} 0) := by
      funext i
      exact i.elim0
    rw [← henv, ev_lift]
    exact lift_mem_lift.mpr (model.constants known)
  steps := by
    intro n Γ l r premises hstep hreq held ρ' sat
    obtain ⟨ρ, rfl, satρ⟩ := sat_lift_down heads consts Γ ρ' sat
    have heldBelow : ∀ premise ∈ premises, Holds heads consts (premise.statement Γ) :=
      fun premise member => (holds_lift_iff heads consts (premise.statement Γ)).mpr (held premise member)
    rw [ev_lift, ev_lift]
    exact congrArg lift (model.steps hstep hreq heldBelow ρ satρ)

end

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
