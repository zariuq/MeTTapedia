import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveDeclarationSpine

/-!
# Typed argument recovery for an arbitrary declaration telescope

Closing an existing context with Pi and applying the declaration to one
simultaneous substitution describe the same dependent argument order. A
formed observed application recovers the whole typed substitution, its
principal result and the original result-adjustment replay. The construction
works for every finite arity rather than a separately unrolled eliminator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive

variable {Head : Type} {R : Rules Head} {n k : Nat}

theorem CtxMor.extend {Γ : Ctx Head k} {Δ : Ctx Head n}
    {substitution : Sub Head k n} {type : Tm Head k} {term : Tm Head n}
    (typed : CtxMor R Γ Δ substitution)
    (termTyped : Typing R Δ term (subst substitution type)) :
    CtxMor R (.snoc Γ type) Δ (consSub term substitution) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [consSub_zero, Ctx.lookup_snoc_zero,
      subst_consSub_rename_wk] using termTyped
  · intro prior
    simpa only [consSub_succ, Ctx.lookup_snoc_succ,
      subst_consSub_rename_wk] using typed prior

theorem CtxMor.dropNewest {Γ : Ctx Head k} {Δ : Ctx Head n} {type : Tm Head k}
    {substitution : Sub Head (k + 1) n}
    (typed : CtxMor R (.snoc Γ type) Δ substitution) :
    CtxMor R Γ Δ (fun i => substitution i.succ) := by
  intro index
  simpa only [Ctx.lookup_snoc_succ, subst_rename, wk] using typed index.succ

namespace DeclarationSpine

/-- Close the existing oldest-to-newest telescope with dependent products. -/
def closeTelescope : {k : Nat} → Ctx Head k → Tm Head k → Tm Head 0
  | _, .nil, result => result
  | _, .snoc telescope domain, result => closeTelescope telescope (.pi domain result)

/-- Apply arguments in telescope order, although substitution lookup uses
newest-first de Bruijn indices. -/
def applyTelescope (function : Tm Head n) :
    {k : Nat} → Ctx Head k → Sub Head k n → Tm Head n
  | _, .nil, _ => function
  | _, .snoc telescope _, substitution =>
      .app (applyTelescope function telescope (fun i => substitution i.succ)) (substitution 0)

private theorem consSub_eta (substitution : Sub Head (k + 1) n) :
    consSub (substitution 0) (fun i => substitution i.succ) = substitution := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

private theorem subst_closed (substitution : Sub Head 0 n) (term : Tm Head 0) :
    subst substitution term = liftClosed term := by
  calc
    subst substitution term = subst (renSub Fin.elim0) term :=
      subst_ext (fun i => Fin.elim0 i) term
    _ = liftClosed term := subst_renSub Fin.elim0 term

/-- An arbitrary observed declaration application supplies a typed
substitution for every declared parameter, plus replay at its exact displayed
result. The Pi boundary is a conversion obligation, not an assumed typing
inversion or a replacement typing judgment. -/
theorem recoverTelescope
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {Γ : Ctx Head n} (context : ContextFormation R Γ)
    (telescope : Ctx Head k) :
    ∀ (result : Tm Head k) (substitution : Sub Head k n)
      {function displayed : Tm Head n},
      DeclarationSpine R Γ function (liftClosed (closeTelescope telescope result)) →
      Typing R Γ (applyTelescope function telescope substitution) displayed →
      CtxMor R telescope Γ substitution ∧
        DeclarationSpine R Γ (applyTelescope function telescope substitution)
          (subst substitution result) ∧
        TypeAdjustment R (subst substitution result) displayed ∧
        (∀ {replacement}, Typing R Γ replacement (subst substitution result) →
          Typing R Γ replacement displayed) := by
  induction telescope with
  | nil =>
      intro result substitution function displayed spine observed
      rw [subst_closed substitution result]
      exact ⟨(fun i => Fin.elim0 i), spine, spine.adjustment boundary observed,
        fun replacement => spine.replay universes boundary context observed replacement⟩
  | @snoc k telescope domain ih =>
      intro result substitution function displayed spine observed
      obtain ⟨_, _, previousObserved, _, _, _⟩ := observed.appGeneration
      obtain ⟨previousTyped, previousSpine, _, _⟩ :=
        ih (.pi domain result) (fun i => substitution i.succ) spine previousObserved
      obtain ⟨argumentTyped, nextSpine, adjustment, replay⟩ :=
        previousSpine.recoverApplication universes boundary context observed
      have opened : inst0 (substitution 0)
          (subst (liftSub (fun i => substitution i.succ)) result) =
          subst substitution result := by
        rw [← subst_consSub, consSub_eta]
      rw [opened] at nextSpine adjustment replay
      have typed := previousTyped.extend argumentTyped
      rw [consSub_eta] at typed
      exact ⟨typed, nextSpine, adjustment, replay⟩

#print axioms closeTelescope
#print axioms applyTelescope
#print axioms recoverTelescope

end DeclarationSpine

#print axioms CtxMor.extend
#print axioms CtxMor.dropNewest

end FormationSensitive
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
