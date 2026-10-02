import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Unguarded
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Transport

/-!
# Curry's paradox for the unguarded recursor

Over the codes, with the carrier `prop` and the identity eliminator `J` into
the universe of proofs, the unguarded unfolding derives `Falsum` in the empty
context (`curry_falsum`):

* `Falsum := ∀ p. p`, `⊤ := Falsum → Falsum` with proof `λ h. h`;
* the relation `R y x := ⊤`, the motive `P x := prop`, and the step
  `F x z := z Falsum (λ h. h) → Falsum`;
* `c := rec P R F Falsum` satisfies `Id prop c (c → Falsum)`, by the unguarded
  unfolding and four β-steps;
* transport along that identity, by `J`, gives `holds c → holds (c → Falsum)`
  and back, hence `holds Falsum`. Both transports are instances of the
  transport of every package with the identity eliminator
  (`Eliminator.transport_typed`).

The guarded recursor needs an accessibility proof of `Falsum` for `R`, and the
guarded package is consistent in a model that computes the recursor
(`AccessibleRecursion.consistent`), so the guard is essential.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (elimType elimTelescope elimBody)
open TelescopeAbstraction (closeType applyClosed)

variable {Head : Type}

namespace Curry

variable (S : Signature Head)

/-- `Falsum := ∀ p. p`, over the carrier `prop`. -/
def bot {n : Nat} : Tm Head n := .app (.const S.point) (.lam (.var 0))

/-- `⊤ := Falsum → Falsum`. -/
def top {n : Nat} : Tm Head n := S.codes.impOf (bot S) (bot S)

/-- `λ h. h`. -/
def triv {n : Nat} : Tm Head n := .lam (.var 0)

/-- The relation `R y x := ⊤`. -/
def rel {n : Nat} : Tm Head n := .lam (.lam (top S))

/-- The motive `P x := prop`. -/
def motive {n : Nat} : Tm Head n := .lam S.codes.propT

/-- The step `F x z := z Falsum (λ h. h) → Falsum`. -/
def step {n : Nat} : Tm Head n :=
  .lam (.lam (S.codes.impOf (.app (.app (.var 0) (bot S)) (triv (Head := Head))) (bot S)))

/-- The type of the step's argument at a point `x`: `Π y. holds (R y x) → P y`. -/
def argType {n : Nat} (x : Tm Head n) : Tm Head n :=
  .pi (liftClosed S.carrier)
    (.pi (S.codes.holdsOf (CodeNames.relOf (rel S) (.var 0) (rename wk x))) (.app (motive S) (.var 1)))

/-- The step's body, under the binder `z`: `z Falsum (λ h. h) → Falsum`. -/
def stepBody {n : Nat} : Tm Head (n + 1) :=
  S.codes.impOf (.app (.app (.var 0) (bot S)) (triv (Head := Head))) (bot S)

/-- The abstraction of the recursive call, `λ y r. rec P R F y`. -/
def callAbs {n : Nat} : Tm Head n :=
  .lam (.lam (S.recSpineU (motive S) (rel S) (step S) (.var 1)))

/-- Curry's code `c := rec P R F Falsum`. -/
def code {n : Nat} : Tm Head n := S.recSpineU (motive S) (rel S) (step S) (bot S)

/-- The unguarded unfolding at Curry's code. -/
def unfoldProof {n : Nat} : Tm Head n := S.unfoldSpineU (motive S) (rel S) (step S) (bot S)

/-- The transport motive `λ y p. holds y`. -/
def forwardMotive {n : Nat} : Tm Head n := transportMotive (S.codes.holdsOf (.var 0))

/-- The transport motive `λ y p. holds y → holds c`. -/
def backwardMotive {n : Nat} : Tm Head n :=
  transportMotive (.pi (S.codes.holdsOf (.var 0)) (S.codes.holdsOf (code S)))

/-- `k := λ h. (J … h …) h : holds (c → Falsum)`. -/
def refuter (J : DeclName) {n : Nat} : Tm Head n :=
  .lam (.app (jSpine J S.codes.propT (code S) (forwardMotive S) (.var 0)
    (S.codes.impOf (code S) (bot S)) (unfoldProof S)) (.var 0))

/-- `w := (J … (λ h. h) …) k : holds c`. -/
def witness (J : DeclName) {n : Nat} : Tm Head n :=
  .app (jSpine J S.codes.propT (code S) (backwardMotive S) (triv (Head := Head))
    (S.codes.impOf (code S) (bot S)) (unfoldProof S)) (refuter S J)

/-- Curry's proof of `Falsum`: `k w`. -/
def proof (J : DeclName) {n : Nat} : Tm Head n := .app (refuter S J) (witness S J)

end Curry

/-- The hypotheses of Curry's derivation: the package's laws, the carrier
`prop`, and the identity eliminator `J` into the universe of proofs, declared in
the base package with a formed type. -/
structure CurryData (S : Signature Head) (J : DeclName) : Prop where
  laws : S.Laws
  carrier : S.carrier = .const S.codes.prop
  jDeclared : S.base.constantType J = some (elimType S.codes.proofs S.codes.proofs)
  jFresh : S.codes.codeType J = none
  jNe : J ≠ S.recursor ∧ J ≠ S.unfold
  jFormed : ∃ w, S.base.isUniverse w ∧
    Typed S.baseRules .nil (elimType S.codes.proofs S.codes.proofs) (.head w)
  /-- The universe of proofs has a type `w`, into which dependent functions from
  proofs to `w` fall. -/
  proofsTyped : ∃ w, S.base.isUniverse w ∧ S.base.headTyping S.codes.proofs w ∧
    ∃ w', S.base.join S.codes.proofs w w' ∧ S.base.cumulative w' w

namespace CurryData

variable {S : Signature Head} {J : DeclName} (D : CurryData S J)
include D

/-- The universes of the unguarded package. -/
theorem universes : S.Universes S.unguardedBase :=
  D.laws.universes.mono D.laws.base_unguardedBase

theorem liftClosed_carrier {n : Nat} :
    (liftClosed S.carrier : Tm Head n) = S.codes.propT := by
  rw [D.carrier]
  rfl

theorem prop_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ S.codes.propT (.head S.codes.proofs) :=
  D.universes.codes.prop_typed

theorem bot_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.bot S) S.codes.propT := by
  have LC := D.universes.codes
  have hvar : Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier)) (.var 0)
      (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  have hlam : Typed S.unguardedRules Γ (.lam (.var 0)) (S.predType S.carrier) := by
    refine .lamIntro LC.predType_typed LC.proofs_universe ?_
    have e : (liftClosed S.carrier : Tm Head (n + 1)) = S.codes.propT := D.liftClosed_carrier
    rw [e] at hvar
    exact hvar
  exact .appElim LC.point_typed hlam

theorem top_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.top S) S.codes.propT :=
  D.universes.codes.impOf_typed D.bot_typed D.bot_typed

theorem triv_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.triv (Head := Head)) (S.codes.holdsOf (Curry.top S)) :=
  D.universes.codes.impIntro D.bot_typed D.bot_typed
    (CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase))

theorem rel_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.rel S) (S.relType S.carrier) := by
  have LC := D.universes.codes
  refine .lamIntro LC.relType_typed LC.proofs_universe
    (.lamIntro (LC.pi_typed LC.carrier_typed' LC.prop_typed) LC.proofs_universe ?_)
  exact D.top_typed

theorem motive_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.motive S) S.motiveType := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := D.universes.top_facts
  exact .lamIntro (D.universes.motiveType_typed hmt toTop piTop) ht
    (D.universes.toMotive D.prop_typed)

theorem bot_carrier {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.bot S) (liftClosed S.carrier) := by
  rw [D.liftClosed_carrier]
  exact D.bot_typed

/-- `R y x ≡ ⊤` at the codes, by two β-steps. -/
theorem rel_beta {n : Nat} {Γ : Ctx Head n} {y x : Tm Head n}
    (hy : Typed S.unguardedRules Γ y (liftClosed S.carrier))
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Equal S.unguardedRules Γ (CodeNames.relOf (Curry.rel S) y x) (Curry.top S) S.codes.propT := by
  have LC := D.universes.codes
  have inner : Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier)) (.lam (Curry.top S))
      (.pi (liftClosed S.carrier) S.codes.propT) :=
    .lamIntro (LC.pi_typed LC.carrier_typed' LC.prop_typed) LC.proofs_universe D.top_typed
  have e1 := Derivable.betaPi LC.relType_typed LC.proofs_universe inner hy
  simp only [inst0, Presentation.subst, subst_liftClosed] at e1
  have e2 := Derivable.appCong e1 (.refl hx)
  have e3 := Derivable.betaPi (LC.pi_typed LC.carrier_typed' LC.prop_typed) LC.proofs_universe
    D.top_typed hx
  exact .trans e2 e3

/-- `P a ≡ prop`, by one β-step. -/
theorem motive_beta {n : Nat} {Γ : Ctx Head n} {a : Tm Head n}
    (ha : Typed S.unguardedRules Γ a (liftClosed S.carrier)) :
    Equal S.unguardedRules Γ (.app (Curry.motive S) a) S.codes.propT (.head S.motive) := by
  obtain ⟨t, ht, hmt, toTop, piTop⟩ := D.universes.top_facts
  exact Derivable.betaPi (D.universes.motiveType_typed hmt toTop piTop) ht
    (D.universes.toMotive D.prop_typed) ha

/-- The type of the step's argument is a type of motives. -/
theorem argType_typed {n : Nat} {Γ : Ctx Head n} {x : Tm Head n}
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Typed S.unguardedRules Γ (Curry.argType S x) (.head S.motive) := by
  have U := D.universes
  have LC := U.codes
  have hy : Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier)) (.var 0)
      (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  have hx' : Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier)) (rename wk x)
      (liftClosed S.carrier) := CodeNames.Laws.weaken_point hx
  have hRel := LC.holdsOf_typed (CodeNames.Laws.relOf_typed D.rel_typed hy hx')
  have hy' : Typed S.unguardedRules (.snoc (.snoc Γ (liftClosed S.carrier))
      (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))) (.var 1)
      (liftClosed S.carrier) := by
    have h := hy.weaken
      (extension := S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))
    simp only [rename_liftClosed] at h
    exact h
  exact U.piMotive (U.toMotive LC.carrier_typed')
    (U.piMotive (U.toMotive hRel) (Signature.motiveApp_typed D.motive_typed hy'))

/-- The step's body at a point `x`: `z Falsum (λ h. h) → Falsum : P x`. -/
theorem stepBody_typed {n : Nat} {Γ : Ctx Head n} {x : Tm Head n}
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Typed S.unguardedRules (.snoc Γ (Curry.argType S x)) (Curry.stepBody S)
      (.app (Curry.motive S) (rename wk x)) := by
  have U := D.universes
  have LC := U.codes
  let Γz : Ctx Head (n + 1) := .snoc Γ (Curry.argType S x)
  have hx' : Typed S.unguardedRules Γz (rename wk x) (liftClosed S.carrier) :=
    CodeNames.Laws.weaken_point hx
  have hz : Typed S.unguardedRules Γz (.var 0)
      (.pi (liftClosed S.carrier)
        (.pi (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk (rename wk x))))
          (.app (Curry.motive S) (.var 1)))) := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase) (Γ := Γ)
      (X := Curry.argType S x)
    simp only [Curry.argType, Presentation.rename, rename_liftClosed, rename_liftRen_wk] at h
    exact h
  have hzb := Derivable.appElim hz D.bot_carrier
  simp only [inst0, Presentation.subst, subst_subst0_rename_wk] at hzb
  have hrel : Equal S.unguardedRules Γz (S.codes.holdsOf (Curry.top S))
      (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (Curry.bot S) (rename wk x)))
      (.head S.codes.proofs) :=
    .symm (CodeNames.Laws.equal_holdsOf LC (D.rel_beta D.bot_carrier hx'))
  have htriv := Derivable.conv D.triv_typed hrel LC.proofs_universe
  have hzbt := Derivable.appElim hzb htriv
  have hzbt' : Typed S.unguardedRules Γz (.app (.app (.var 0) (Curry.bot S))
      (Curry.triv (Head := Head))) S.codes.propT :=
    Derivable.conv hzbt (D.motive_beta D.bot_carrier) U.motive_universe
  exact .conv (LC.impOf_typed hzbt' D.bot_typed) (.symm (D.motive_beta hx')) U.motive_universe

theorem stepInner_formed {n : Nat} {Γ : Ctx Head n} {x : Tm Head n}
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Typed S.unguardedRules Γ (.pi (Curry.argType S x) (.app (Curry.motive S) (rename wk x)))
      (.head S.motive) :=
  D.universes.piMotive (D.argType_typed hx)
    (Signature.motiveApp_typed D.motive_typed (CodeNames.Laws.weaken_point hx))

omit D in
theorem stepType_eq {n : Nat} :
    (S.stepTypeOf (Curry.motive S) (Curry.rel S) : Tm Head n) =
      .pi (liftClosed S.carrier)
        (.pi (Curry.argType S (.var 0)) (.app (Curry.motive S) (.var 1))) := by
  rw [Signature.stepTypeOf_eq]
  rfl

theorem stepType_formed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (S.stepTypeOf (Curry.motive S) (Curry.rel S)) (.head S.motive) := by
  rw [stepType_eq]
  exact D.universes.piMotive (D.universes.toMotive D.universes.codes.carrier_typed')
    (D.stepInner_formed CodeNames.Laws.var_carrier)

/-- The step's inner abstraction at a point `x`. -/
theorem stepInner_typed {n : Nat} {Γ : Ctx Head n} {x : Tm Head n}
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Typed S.unguardedRules Γ (.lam (Curry.stepBody S))
      (.pi (Curry.argType S x) (.app (Curry.motive S) (rename wk x))) :=
  .lamIntro (D.stepInner_formed hx) D.universes.motive_universe (D.stepBody_typed hx)

/-- The step is a step function for the motive and the relation. -/
theorem step_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.step S) (S.stepTypeOf (Curry.motive S) (Curry.rel S)) := by
  have hf := D.stepType_formed (Γ := Γ)
  rw [stepType_eq] at hf ⊢
  exact Derivable.lamIntro hf D.universes.motive_universe
    (D.stepInner_typed (Γ := .snoc Γ (liftClosed S.carrier)) (x := .var 0) CodeNames.Laws.var_carrier)

/-! ## Transport along an identity of codes -/

/-- `J` is declared in the unguarded package at its type. -/
theorem j_declared :
    S.unguardedRules.constantType J = some (elimType S.codes.proofs S.codes.proofs) := by
  have e : S.unguardedBase.constantType J = S.base.constantType J := by
    simp [Signature.unguardedBase, D.jNe.1, D.jNe.2]
  simp [Codes.extend, D.jFresh, Option.orElse, e, D.jDeclared]

/-- **The identity eliminator of the unguarded package**, with carriers and
motives in the universe of proofs. -/
theorem eliminator : Eliminator S.unguardedRules J S.codes.proofs S.codes.proofs where
  declared := D.j_declared
  formed := by
    obtain ⟨w, hw, typed⟩ := D.jFormed
    exact ⟨w, hw, (D.laws.base_unguardedBase.codes S.codes).derivable typed⟩
  carrier_universe := D.universes.codes.proofs_universe
  motive_universe := D.universes.codes.proofs_universe
  above := by
    obtain ⟨w, hw, hU, w', hj, hc⟩ := D.proofsTyped
    exact ⟨w, hw, hU, w', hj, hc⟩

/-! ## Curry's code and its unfolding -/

theorem code_at_motive {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.code S) (.app (Curry.motive S) (Curry.bot S)) :=
  D.universes.recU_apply (Signature.unguardedRules_constantType_recursor D.laws) D.motive_typed
    D.rel_typed D.step_typed D.bot_carrier

theorem code_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.code S) S.codes.propT :=
  .conv D.code_at_motive (D.motive_beta D.bot_carrier) D.universes.motive_universe

/-- The inner abstraction `λ r. rec P R F y` of the recursive call. -/
theorem callInner_typed {n : Nat} {Γ : Ctx Head n} {x : Tm Head n}
    (hx : Typed S.unguardedRules Γ x (liftClosed S.carrier)) :
    Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier))
        (.lam (S.recSpineU (Curry.motive S) (Curry.rel S) (Curry.step S) (.var 1)))
        (.pi (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))
          (.app (Curry.motive S) (.var 1))) ∧
      Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier))
        (.pi (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))
          (.app (Curry.motive S) (.var 1))) (.head S.motive) := by
  have U := D.universes
  have LC := U.codes
  have hy : Typed S.unguardedRules (.snoc Γ (liftClosed S.carrier)) (.var 0)
      (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  have hx' := CodeNames.Laws.weaken_point (E := liftClosed S.carrier) hx
  have hRel := LC.holdsOf_typed (CodeNames.Laws.relOf_typed D.rel_typed hy hx')
  have hy' : Typed S.unguardedRules (.snoc (.snoc Γ (liftClosed S.carrier))
      (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))) (.var 1)
      (liftClosed S.carrier) := by
    have h := hy.weaken
      (extension := S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (.var 0) (rename wk x)))
    simp only [rename_liftClosed] at h
    exact h
  have formed := U.piMotive (U.toMotive hRel) (Signature.motiveApp_typed D.motive_typed hy')
  refine ⟨.lamIntro formed U.motive_universe ?_, formed⟩
  exact U.recU_apply (Signature.unguardedRules_constantType_recursor D.laws) D.motive_typed
    D.rel_typed D.step_typed hy'

theorem callAbs_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.callAbs S) (Curry.argType S (Curry.bot S)) :=
  .lamIntro (D.argType_typed D.bot_carrier) D.universes.motive_universe
    (D.callInner_typed D.bot_carrier).1

/-- **The unguarded unfolding at Curry's code is `c → Falsum`**, by four β-steps. -/
theorem unfolding_eq {n : Nat} {Γ : Ctx Head n} :
    Equal S.unguardedRules Γ (S.unfoldingU (Curry.motive S) (Curry.rel S) (Curry.step S) (Curry.bot S))
      (S.codes.impOf (Curry.code S) (Curry.bot S)) (.app (Curry.motive S) (Curry.bot S)) := by
  have U := D.universes
  have LC := U.codes
  -- `F Falsum ≡ λ z. z Falsum (λ h. h) → Falsum`
  have hf := D.stepType_formed (Γ := Γ)
  rw [stepType_eq] at hf
  have e1 := Derivable.betaPi hf U.motive_universe
    (D.stepInner_typed (Γ := .snoc Γ (liftClosed S.carrier)) (x := .var 0) CodeNames.Laws.var_carrier)
    D.bot_carrier
  have e1' : Equal S.unguardedRules Γ (.app (Curry.step S) (Curry.bot S)) (.lam (Curry.stepBody S))
      (.pi (Curry.argType S (Curry.bot S)) (.app (Curry.motive S) (rename wk (Curry.bot S)))) := by
    simp only [inst0, Presentation.subst, Curry.argType, subst_liftClosed] at e1
    exact e1
  have e2 := Derivable.appCong e1' (.refl D.callAbs_typed)
  have e3 := Derivable.betaPi (D.stepInner_formed (Γ := Γ) D.bot_carrier) U.motive_universe
    (D.stepBody_typed (Γ := Γ) D.bot_carrier) (D.callAbs_typed (Γ := Γ))
  -- the recursive call at `Falsum`, with the proof `λ h. h` of `R Falsum Falsum`
  have hinner := D.callInner_typed (Γ := Γ) D.bot_carrier
  have e4a := Derivable.betaPi (D.argType_typed (Γ := Γ) D.bot_carrier) U.motive_universe hinner.1
    (D.bot_carrier (Γ := Γ))
  have triv' : Typed S.unguardedRules Γ (Curry.triv (Head := Head))
      (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (Curry.bot S) (Curry.bot S))) :=
    .conv D.triv_typed (.symm (CodeNames.Laws.equal_holdsOf LC (D.rel_beta D.bot_carrier D.bot_carrier)))
      LC.proofs_universe
  have e4a' : Equal S.unguardedRules Γ (.app (Curry.callAbs S) (Curry.bot S))
      (.lam (S.recSpineU (Curry.motive S) (Curry.rel S) (Curry.step S) (rename wk (Curry.bot S))))
      (.pi (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (Curry.bot S) (Curry.bot S)))
        (.app (Curry.motive S) (rename wk (Curry.bot S)))) := by
    simp only [inst0, Presentation.subst] at e4a
    exact e4a
  have e4b := Derivable.appCong e4a' (.refl triv')
  have hbot' : Typed S.unguardedRules
      (.snoc Γ (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (Curry.bot S) (Curry.bot S))))
      (rename wk (Curry.bot S)) (liftClosed S.carrier) := CodeNames.Laws.weaken_point D.bot_carrier
  have hcall := U.recU_apply (Signature.unguardedRules_constantType_recursor D.laws) D.motive_typed
    D.rel_typed D.step_typed hbot'
  have formedR : Typed S.unguardedRules Γ
      (.pi (S.codes.holdsOf (CodeNames.relOf (Curry.rel S) (Curry.bot S) (Curry.bot S)))
        (.app (Curry.motive S) (rename wk (Curry.bot S)))) (.head S.motive) :=
    U.piMotive (U.toMotive (LC.holdsOf_typed (CodeNames.Laws.relOf_typed D.rel_typed D.bot_carrier
      D.bot_carrier))) (Signature.motiveApp_typed D.motive_typed hbot')
  have e4c := Derivable.betaPi formedR U.motive_universe hcall triv'
  have e4 : Equal S.unguardedRules Γ
      (.app (.app (Curry.callAbs S) (Curry.bot S)) (Curry.triv (Head := Head))) (Curry.code S)
      S.codes.propT :=
    .convEq (.trans e4b e4c) (D.motive_beta D.bot_carrier) U.motive_universe
  have e5 := Derivable.appCong (Derivable.appCong (.refl LC.imp_typed) e4) (.refl D.bot_typed)
  have e5' : Equal S.unguardedRules Γ
      (S.codes.impOf (.app (.app (Curry.callAbs S) (Curry.bot S)) (Curry.triv (Head := Head)))
        (Curry.bot S))
      (S.codes.impOf (Curry.code S) (Curry.bot S)) (.app (Curry.motive S) (Curry.bot S)) :=
    .convEq e5 (.symm (D.motive_beta D.bot_carrier)) U.motive_universe
  exact .trans e2 (.trans e3 e5')

/-- **Curry's identity**: `Id prop c (c → Falsum)`, by the unguarded unfolding. -/
theorem unfoldProof_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.unfoldProof S)
      (.id S.codes.propT (Curry.code S) (S.codes.impOf (Curry.code S) (Curry.bot S))) := by
  have U := D.universes
  have h := U.unfoldU_apply (Signature.unguardedRules_constantType_recursor D.laws)
    (Signature.unguardedRules_constantType_unfold D.laws) D.motive_typed D.rel_typed D.step_typed
    D.bot_carrier (Γ := Γ)
  exact .conv h (.idCong (D.motive_beta D.bot_carrier) U.motive_universe (.refl D.code_at_motive)
    D.unfolding_eq) U.motive_universe

/-! ## Transport along Curry's identity -/

/-- **Forward transport**: from `holds c`, `holds (c → Falsum)`. -/
theorem forward {n : Nat} {Γ : Ctx Head n} {h : Tm Head n}
    (hh : Typed S.unguardedRules Γ h (S.codes.holdsOf (Curry.code S))) :
    Typed S.unguardedRules Γ
      (jSpine J S.codes.propT (Curry.code S) (Curry.forwardMotive S) h
        (S.codes.impOf (Curry.code S) (Curry.bot S)) (Curry.unfoldProof S))
      (S.codes.holdsOf (S.codes.impOf (Curry.code S) (Curry.bot S))) := by
  have LC := D.universes.codes
  have hB : Typed S.unguardedRules (.snoc Γ S.codes.propT) (S.codes.holdsOf (.var 0))
      (.head S.codes.proofs) :=
    LC.holdsOf_typed (CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase))
  exact D.eliminator.transport_typed D.prop_typed D.code_typed
    (LC.impOf_typed D.code_typed D.bot_typed) D.unfoldProof_typed hB hh

/-- **Backward transport**: `holds (c → Falsum) → holds c`. -/
theorem backward {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ
      (jSpine J S.codes.propT (Curry.code S) (Curry.backwardMotive S) (Curry.triv (Head := Head))
        (S.codes.impOf (Curry.code S) (Curry.bot S)) (Curry.unfoldProof S))
      (.pi (S.codes.holdsOf (S.codes.impOf (Curry.code S) (Curry.bot S)))
        (S.codes.holdsOf (Curry.code S))) := by
  have LC := D.universes.codes
  have hv : Typed S.unguardedRules (.snoc Γ S.codes.propT) (.var 0) S.codes.propT :=
    CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase)
  have hB : Typed S.unguardedRules (.snoc Γ S.codes.propT)
      (.pi (S.codes.holdsOf (.var 0)) (S.codes.holdsOf (Curry.code S))) (.head S.codes.proofs) :=
    LC.pi_typed (LC.holdsOf_typed hv) (LC.holdsOf_typed D.code_typed)
  have hid : Typed S.unguardedRules Γ (Curry.triv (Head := Head))
      (.pi (S.codes.holdsOf (Curry.code S)) (S.codes.holdsOf (Curry.code S))) :=
    .lamIntro (LC.pi_typed (LC.holdsOf_typed D.code_typed) (LC.holdsOf_typed D.code_typed))
      LC.proofs_universe (CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase))
  exact D.eliminator.transport_typed D.prop_typed D.code_typed
    (LC.impOf_typed D.code_typed D.bot_typed) D.unfoldProof_typed hB hid

/-! ## Curry's paradox -/

theorem refuter_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.refuter S J)
      (S.codes.holdsOf (S.codes.impOf (Curry.code S) (Curry.bot S))) := by
  have LC := D.universes.codes
  have hh : Typed S.unguardedRules (.snoc Γ (S.codes.holdsOf (Curry.code S))) (.var 0)
      (S.codes.holdsOf (Curry.code S)) :=
    CodeNames.Laws.var_zero (C := S.toCodeNames) (B := S.unguardedBase)
  exact LC.impIntro D.code_typed D.bot_typed
    (LC.impElim D.code_typed D.bot_typed (D.forward hh) hh)

theorem witness_typed {n : Nat} {Γ : Ctx Head n} :
    Typed S.unguardedRules Γ (Curry.witness S J) (S.codes.holdsOf (Curry.code S)) :=
  .appElim D.backward D.refuter_typed

/-- **Curry's paradox.** Without the guard, the unfolding derives `Falsum` in the
empty context. -/
theorem curry_falsum :
    Typed S.unguardedRules .nil (Curry.proof S J) (S.codes.holdsOf (Curry.bot S)) :=
  D.universes.codes.impElim D.code_typed D.bot_typed D.refuter_typed D.witness_typed

end CurryData

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
