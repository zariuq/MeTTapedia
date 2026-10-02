import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Progress

/-!
# A computing constant with no root step

One inductive type, its constructor, and one computing constant. The computing
constant inspects its only argument, and the constructor is a canonical form of
that argument's type. The package declares no root computation, so that
canonical scrutinee has no root step.

The application of the computing constant to the constructor is typed at a
universe in the empty context. It takes no annotated weak-head step, and its
erasure is not a weak-head normal form of a type. Progress fails for a typed
term of a universe, and the root-step obligation is the fact that fails.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace ProgressGap

open Normalization
open Progress (ScrutineeCanonical)

inductive GapHead where
  | u0
  | u1
  deriving DecidableEq

def bitName : DeclName := `bit
def ttName : DeclName := `tt
def badName : DeclName := `bad

def gapHeadTyping : GapHead → GapHead → Prop
  | .u0, .u1 => True
  | .u1, .u1 => True
  | _, _ => False

def gapUniverse : GapHead → Prop
  | .u0 => True
  | .u1 => True

def gapJoin : GapHead → GapHead → GapHead → Prop
  | .u0, .u1, .u0 => True
  | .u1, .u1, .u1 => True
  | _, _, _ => False

def gapConstType : DeclName → Option (Tm GapHead 0)
  | name =>
    if name = bitName then some (.head .u0)
    else if name = ttName then some (.const bitName)
    else if name = badName then some (.pi (.const bitName) (.head .u0))
    else none

def gapRules : Rules GapHead where
  headTyping := gapHeadTyping
  isUniverse := gapUniverse
  join := gapJoin
  cumulative := fun u v => u = v
  headEq := fun u v => u = v
  constantType := gapConstType
  computation := .empty

def gapConstTypeA : DeclName → Option (CTm GapHead 0)
  | name =>
    if name = bitName then some (.head .u0)
    else if name = ttName then some (.const bitName)
    else if name = badName then some (.pi (.const bitName) (.head .u0))
    else none

def gapChurch : ChurchRules gapRules where
  constantType := gapConstTypeA
  computation := .empty
  erase_constantType := fun name => by
    by_cases hb : name = bitName
    · subst hb; rfl
    by_cases ht : name = ttName
    · subst ht; rfl
    by_cases hd : name = badName
    · subst hd; rfl
    simp only [gapRules, gapConstType, gapConstTypeA, hb, ht, hd, if_false, Option.map_none]
  erase_step := fun impossible => impossible.elim

def gapRoles : Roles GapHead := fun name =>
  if name = bitName then .inductive [(ttName, ([] : List (Field GapHead)))]
  else if name = ttName then .constructor 0
  else if name = badName then .computes 1 (.split 0 .constructor fun _ => .leaf)
  else .rigid

theorem gapRoles_bit : gapRoles bitName = .inductive [(ttName, [])] := by
  simp [gapRoles, bitName]

theorem gapRoles_tt : gapRoles ttName = .constructor 0 := by
  have hb : ttName ≠ bitName := by decide
  rw [gapRoles, if_neg hb, if_pos rfl]

theorem gapRoles_bad :
    gapRoles badName = .computes 1 (.split 0 .constructor fun _ => .leaf) := by
  have hb : badName ≠ bitName := by decide
  have ht : badName ≠ ttName := by decide
  rw [gapRoles, if_neg hb, if_neg ht, if_pos rfl]

theorem declared_bit : gapChurch.constantType bitName = some (.head .u0) := by
  simp [gapChurch, gapConstTypeA, bitName]

theorem declared_tt : gapChurch.constantType ttName = some (.const bitName) := by
  have hb : ttName ≠ bitName := by decide
  change gapConstTypeA ttName = some (.const bitName)
  rw [gapConstTypeA, if_neg hb, if_pos rfl]

theorem declared_bad :
    gapChurch.constantType badName = some (.pi (.const bitName) (.head .u0)) := by
  have hb : badName ≠ bitName := by decide
  have ht : badName ≠ ttName := by decide
  change gapConstTypeA badName = some (.pi (.const bitName) (.head .u0))
  rw [gapConstTypeA, if_neg hb, if_neg ht, if_pos rfl]

theorem bit_type_typed : CTyped gapChurch .nil (.head .u0) (.head .u1) :=
  .headType trivial

theorem bit_typed {n : Nat} (Γ : CCtx GapHead n) :
    CTyped gapChurch Γ (.const bitName) (.head .u0) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_bit bit_type_typed trivial)

theorem tt_typed {n : Nat} (Γ : CCtx GapHead n) :
    CTyped gapChurch Γ (.const ttName) (.const bitName) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_tt (bit_typed .nil) trivial)

theorem bad_type_typed :
    CTyped gapChurch .nil (.pi (.const bitName) (.head .u0)) (.head .u0) :=
  .piForm (u := GapHead.u0) (v := GapHead.u1) (w := GapHead.u0) (bit_typed .nil) trivial
    (.headType trivial) trivial trivial

theorem bad_typed {n : Nat} (Γ : CCtx GapHead n) :
    CTyped gapChurch Γ (.const badName) (.pi (.const bitName) (.head .u0)) := by
  simpa [CTm.liftClosed, CTm.rename] using
    (CDerivable.const (Γ := Γ) declared_bad bad_type_typed trivial)

def gapTerm : CTm GapHead 0 := .app (.const badName) (.const ttName)

theorem gap_typed : CTyped gapChurch .nil gapTerm (.head .u0) := by
  simpa [gapTerm, CTm.inst0, CTm.subst, CTm.subst0] using
    (CDerivable.appElim (bad_typed .nil) (tt_typed .nil))

theorem gap_formed : CCtxFormed gapChurch (.nil : CCtx GapHead 0) := .nil

theorem gap_universe : gapRules.isUniverse .u0 := trivial

/-- The constructor is a canonical scrutinee of the computing constant. -/
theorem gap_scrutinee :
    ScrutineeCanonical gapChurch gapRoles (.split 0 .constructor fun _ => .leaf)
      (.pi (.const bitName) (.head .u0))
      ([.const ttName] : List (CTm GapHead 0)) :=
  ⟨[], .const ttName, [], rfl, rfl, .inl ⟨bitName, by decide,
    ⟨ttName, 0, [], .const bitName, gapRoles_tt, rfl, rfl, declared_tt, by decide⟩⟩⟩

theorem gap_root_fails :
    ¬ ∃ r : CTm GapHead 0,
        gapChurch.computation.step (CTm.appSpine (.const badName) [.const ttName]) r := by
  intro ⟨_, step⟩
  exact step.elim

theorem gap_rootCoverage_fails :
    ¬ (∀ {n : Nat} (args : List (CTm GapHead n)), args.length = 1 →
        ScrutineeCanonical gapChurch gapRoles (.split 0 .constructor fun _ => .leaf)
          (.pi (.const bitName) (.head .u0)) args →
        ∃ r, gapChurch.computation.step (CTm.appSpine (.const badName) args) r) := by
  intro cover
  exact gap_root_fails (cover (n := 0) [.const ttName] rfl gap_scrutinee)

theorem gap_not_arity_zero (c : DeclName) {inspect : InspectTree} :
    gapRoles c ≠ .computes 0 inspect := by
  intro role
  by_cases hb : c = bitName
  · subst hb
    rw [gapRoles_bit] at role
    cases role
  by_cases ht : c = ttName
  · subst ht
    rw [gapRoles_tt] at role
    cases role
  by_cases hd : c = badName
  · subst hd
    rw [gapRoles_bad] at role
    injection role with h
    cases h
  · rw [gapRoles, if_neg hb, if_neg ht, if_neg hd] at role
    cases role

theorem const_no_whstep {n : Nat} {c : DeclName} {u : Tm GapHead n} :
    ¬ WhStep gapRules gapRoles (.const c) u := by
  intro step
  generalize e : (.const c : Tm GapHead n) = t at step
  cases step with
  | beta _ _ => cases e
  | fstPair _ _ => cases e
  | sndPair _ _ => cases e
  | root h => exact h.elim
  | appFun _ => cases e
  | fst _ => cases e
  | snd _ => cases e
  | @scrutinee c' _ _ args _ _ _ _ role length _ _ =>
      have eq : appSpine (.const c') args = appSpine (.const c) ([] : List (Tm GapHead n)) := by
        rw [appSpine_nil]
        exact e.symm
      obtain ⟨names, rfl⟩ := appSpine_const_injective eq
      subst names
      subst length
      exact gap_not_arity_zero c' role

/-- The erased application takes no weak-head step. -/
theorem gapTerm_whnf : Whnf gapRules gapRoles gapTerm.erase := by
  intro u step
  simp only [gapTerm, CTm.erase] at step
  generalize e : (.app (.const badName) (.const ttName) : Tm GapHead 0) = t at step
  cases step with
  | beta _ _ => cases e
  | fstPair _ _ => cases e
  | sndPair _ _ => cases e
  | root h => exact h.elim
  | appFun inner =>
      obtain ⟨hf, _⟩ := Tm.app.inj e
      subst hf
      exact const_no_whstep inner
  | fst _ => cases e
  | snd _ => cases e
  | scrutinee role _ focus inner =>
      obtain ⟨init, rfl, hf⟩ := appSpine_const_eq_app e.symm
      cases init with
      | nil =>
          rw [appSpine_nil] at hf
          cases hf
          rw [gapRoles_bad] at role
          cases role
          obtain ⟨before, after, hlen, hv, _, hk⟩ := InspectTree.Focus.single focus
          obtain rfl := List.eq_nil_of_length_eq_zero hlen
          obtain ⟨rfl, rfl⟩ := List.cons.inj hv
          cases hk
          exact const_no_whstep inner
      | cons b bs =>
          obtain ⟨_, _, happ⟩ := appSpine_ne_nil_eq_app (as := b :: bs) (by intro h; cases h)
          rw [happ] at hf
          cases hf

theorem gapTerm_no_step {t : CTm GapHead 0} : ¬ CWhStepR gapChurch gapRoles gapTerm t :=
  CWhStepR.not_of_whnf gapTerm_whnf t

theorem bare_not_neutral {n : Nat} {c : DeclName} (notRigid : gapRoles c ≠ .rigid)
    (notArityZero : ∀ inspect, gapRoles c ≠ .computes 0 inspect)
    (neutral : Neutral gapRoles (.const c : Tm GapHead n)) : False := by
  rcases Neutral.constSpine neutral (appSpine_nil (.const c)).symm with
      role | ⟨arity, inspect, pre, post, _, _, roleC, happ, plen, _, _, _⟩
  · exact notRigid role
  · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp happ.symm
    cases plen
    exact notArityZero inspect roleC

theorem gapTerm_not_neutral :
    ¬ Neutral gapRoles (.app (.const badName) (.const ttName) : Tm GapHead 0) := by
  intro neutral
  have spine : (.app (.const badName) (.const ttName) : Tm GapHead 0) =
      appSpine (.const badName) [.const ttName] := rfl
  rcases Neutral.constSpine neutral spine with
      role | ⟨_, _, pre, post, _, _, roleC, happ, plen, focus, inner, _⟩
  · rw [gapRoles_bad] at role
    cases role
  · rw [gapRoles_bad] at roleC
    cases roleC
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp plen
    have happ' : a :: post = .const ttName :: ([] : List (Tm GapHead 0)) := by
      rw [← List.singleton_append]
      exact happ.symm
    obtain ⟨rfl, rfl⟩ := List.cons.inj happ'
    obtain ⟨_, _, hlen, hv, _, hk⟩ := InspectTree.Focus.single focus
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    obtain ⟨rfl, rfl⟩ := List.cons.inj hv
    cases hk
    exact bare_not_neutral
      (by rw [gapRoles_tt]; nofun)
      (fun _ role => by rw [gapRoles_tt] at role; cases role) inner

theorem gapTerm_not_typeForm : ¬ IsTypeForm gapRoles gapTerm.erase := by
  intro form
  simp only [gapTerm, CTm.erase] at form
  rcases form with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | neutral | ⟨_, _, _, h⟩
  · cases h
  · cases h
  · cases h
  · cases h
  · exact gapTerm_not_neutral neutral
  · cases h

/-- **Progress fails.** The term is typed at a universe in the empty context, and it
neither takes a weak-head step nor erases to a weak-head normal form of a type. -/
theorem gap_no_progress :
    ¬ ((∃ t, CWhStepR gapChurch gapRoles gapTerm t) ∨ IsTypeForm gapRoles gapTerm.erase) := by
  intro outcome
  rcases outcome with ⟨_, step⟩ | form
  · exact gapTerm_no_step step
  · exact gapTerm_not_typeForm form

end ProgressGap
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
