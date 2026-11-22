import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# A rigid constant with a witness

Adding one constant, and no root step, at a closed type that already has a
closed inhabitant, does not change what the judgment derives about terms in
which the constant does not occur, and it does not add an inhabitant of such
a type. Strong normalization of typed terms is kept, because the new constant
is rigid: a reduction step does not unfold it, and replacing it by the
witness sends each step to one step.

Rigidity is necessary: a root step from a constant to itself is a term with no
normal form, by the same accessibility argument as a looping reduction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open StrongNormalization

variable {Head : Type}

/-! ## The extension -/

/-- `R` with one further declaration `c : T` and no further root step. -/
def _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Rules.addConstant
    (R : Rules Head) (c : DeclName) (T : Tm Head 0) : Rules Head where
  headTyping := R.headTyping
  isUniverse := R.isUniverse
  join := R.join
  cumulative := R.cumulative
  headEq := R.headEq
  constantType d := cond (d == c) (some T) (R.constantType d)
  computation := R.computation

/-- The hypotheses under which the added constant is conservative. `c` is not
declared in `R` and it occurs in no declared type of `R`, nor in `T` itself.
Replacing `c` by the witness sends each root step of `R` to a root step.
`T` is a closed type of `R`, and `w` is a closed term of that type. -/
structure Witnessed (R : Rules Head) where
  name : DeclName
  type : Tm Head 0
  witness : Tm Head 0
  fresh : R.constantType name = none
  typesAbsent : ∀ {d : DeclName} {T : Tm Head 0},
    R.constantType d = some T → T.allConstants (fun n => !(n == name)) = true
  /-- Replacing `name` by `witness` sends each root step to a root step.
  A root step is a substitution instance of a rule, so the new constant may
  stand in an argument of a step even when the rule itself does not mention
  it; absence from every step term is sufficient (`Rules.computation_fixed`)
  and this stability is what the instantiation uses. -/
  stepsStable : ∀ {k : Nat} {l r : Tm Head k},
    R.computation.step l r →
    R.computation.step
      (l.instConsts (fun d => cond (d == name) witness (.const d)))
      (r.instConsts (fun d => cond (d == name) witness (.const d)))
  typeAbsent : type.allConstants (fun n => !(n == name)) = true
  universeHead : Head
  universeOk : R.isUniverse universeHead
  typeTyped : Typed R .nil type (.head universeHead)
  inhabited : Typed R .nil witness type

namespace Witnessed

variable {R : Rules Head}

/-- Replace the new constant by the witness and leave every other constant. -/
def subst (W : Witnessed R) : DeclName → Tm Head 0 :=
  fun d => cond (d == W.name) W.witness (.const d)

theorem fixes (W : Witnessed R) (d : DeclName)
    (h : (!(d == W.name)) = true) : W.subst d = .const d := by
  cases hb : d == W.name with
  | false => simp only [subst, hb, cond_false]
  | true =>
      rw [hb] at h
      exact (Bool.false_ne_true h).elim

end Witnessed

/-- A derivation of `R` remains a derivation after the constant is declared. -/
theorem RulesRenaming.to_addConstant {R : Rules Head} {c : DeclName} {T : Tm Head 0}
    (fresh : R.constantType c = none) :
    RulesRenaming R (R.addConstant c T) (fun name => name) where
  headTyping h := h
  isUniverse h := h
  join h := h
  cumulative h := h
  headEq h := h
  constantType := by
    intro name type declared
    rw [Tm.mapConst_id]
    cases hb : name == c with
    | false =>
        simp only [Rules.addConstant, hb, cond_false]
        exact declared
    | true =>
        have hd : name = c := LawfulBEq.eq_of_beq hb
        rw [hd] at declared
        nomatch fresh.symm.trans declared
  computation := by
    intro n l r step
    rw [Tm.mapConst_id, Tm.mapConst_id]
    exact step

theorem Statement.mapConst_id (st : Statement Head) :
    st.mapConst (fun name => name) = st := by
  cases st <;>
    simp only [Statement.mapConst, Tm.mapConst_id, Ctx.mapConst_id]

theorem Derivable.to_addConstant {R : Rules Head} {c : DeclName} {T : Tm Head 0}
    (fresh : R.constantType c = none) {st : Statement Head} (derivation : Derivable R st) :
    Derivable (R.addConstant c T) st := by
  have moved :=
    Derivable.mapConst (RulesRenaming.to_addConstant (T := T) fresh) derivation
  rw [Statement.mapConst_id] at moved
  exact moved

theorem Typed.to_addConstant {R : Rules Head} {c : DeclName} {T : Tm Head 0}
    (fresh : R.constantType c = none) {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (typed : Typed R Γ t A) : Typed (R.addConstant c T) Γ t A :=
  Derivable.to_addConstant fresh typed

namespace Witnessed

variable {R : Rules Head}

/-- The extension instantiates back into `R` by reading the new constant as
the witness. -/
theorem rulesInstance (W : Witnessed R) :
    RulesInstance (R.addConstant W.name W.type) R W.subst where
  headTyping h := h
  isUniverse h := h
  join h := h
  cumulative h := h
  headEq h := h
  typed := by
    intro d T u declared formed hu
    cases hb : d == W.name with
    | true =>
        have hd : d = W.name := LawfulBEq.eq_of_beq hb
        have declaredType : (R.addConstant W.name W.type).constantType d = some W.type := by
          simp only [Rules.addConstant, hb, cond_true]
        rw [declaredType] at declared
        have hT : W.type = T := by
          injection declared
        have typeId : (W.type.instConsts W.subst) = W.type :=
          Tm.instConsts_of_allConstants W.subst W.fixes W.typeAbsent
        have witnessSubst : W.subst d = W.witness := by
          simp only [subst, hb, cond_true]
        rw [← hT, typeId, witnessSubst]
        exact W.inhabited
    | false =>
        have declaredR : R.constantType d = some T := by
          have same : (R.addConstant W.name W.type).constantType d = R.constantType d := by
            simp only [Rules.addConstant, hb, cond_false]
          rw [same] at declared
          exact declared
        have typeId : T.instConsts W.subst = T :=
          Tm.instConsts_of_allConstants W.subst W.fixes (W.typesAbsent declaredR)
        rw [typeId] at formed ⊢
        have asConst : W.subst d = .const d := by
          simp only [subst, hb, cond_false]
        rw [asConst]
        have typedConst := Derivable.const (Γ := .nil) declaredR formed hu
        rw [Tm.liftClosed_at_zero] at typedConst
        exact typedConst
  computation := by
    intro n l r step
    exact W.stepsStable step

/-- **Conservativity.** A statement derivable in the extension is derivable in
`R` after the new constant is replaced by the witness. -/
theorem conserves (W : Witnessed R) {st : Statement Head}
    (derivation : Derivable (R.addConstant W.name W.type) st) :
    Derivable R (st.instConsts W.subst) :=
  Derivable.instConsts W.rulesInstance derivation

/-- A statement in which the new constant does not occur is derivable in `R`
as it stands. -/
theorem conserves_absent (W : Witnessed R) {st : Statement Head}
    (absent : st.allConstants (fun n => !(n == W.name)) = true)
    (derivation : Derivable (R.addConstant W.name W.type) st) :
    Derivable R st := by
  have moved := W.conserves derivation
  rw [Statement.instConsts_of_allConstants W.subst W.fixes absent] at moved
  exact moved

/-- **Consistency is kept.** A closed type in which the new constant does not
occur gains no closed inhabitant. -/
theorem consistent (W : Witnessed R) {E : Tm Head 0}
    (absent : E.allConstants (fun n => !(n == W.name)) = true)
    (empty : ∀ t : Tm Head 0, ¬ Typed R .nil t E) {t : Tm Head 0} :
    ¬ Typed (R.addConstant W.name W.type) .nil t E := by
  intro typed
  have moved := Typed.instConsts W.rulesInstance typed
  have typeId : E.instConsts W.subst = E :=
    Tm.instConsts_of_allConstants W.subst W.fixes absent
  rw [typeId] at moved
  exact empty (t.instConsts W.subst) moved

theorem formed_instConsts (W : Witnessed R) :
    ∀ {n : Nat} {Γ : Ctx Head n}, CtxFormed (R.addConstant W.name W.type) Γ →
      CtxFormed R (Γ.instConsts W.subst)
  | _, _, .nil => .nil
  | _, _, .snoc formed ⟨u, hu, typed⟩ =>
      .snoc (formed_instConsts W formed)
        ⟨u, W.rulesInstance.isUniverse hu, typed.instConsts W.rulesInstance⟩

/-- **Strong normalization is kept.** If every term typed in a formed context
of `R` is strongly normalizing, the same holds in the extension. -/
theorem strong_normalization (W : Witnessed R)
    (allSN : ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n},
      CtxFormed R Γ → Typed R Γ t A → SN R t)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}
    (formed : CtxFormed (R.addConstant W.name W.type) Γ)
    (typed : Typed (R.addConstant W.name W.type) Γ t A) :
    SN (R.addConstant W.name W.type) t := by
  have snImage : SN R (t.instConsts W.subst) :=
    allSN (W.formed_instConsts formed) (typed.instConsts W.rulesInstance)
  have snBase : SN R t :=
    SN.of_instConsts W.subst (fun step => W.stepsStable step) snImage
  exact snBase

/-- The new constant is a term of its declared type, so the extension derives
a statement in which the constant occurs. -/
theorem typed_const (W : Witnessed R) :
    Typed (R.addConstant W.name W.type) .nil (.const W.name) W.type := by
  have formed := Typed.to_addConstant (T := W.type) W.fresh W.typeTyped
  have declared : (R.addConstant W.name W.type).constantType W.name = some W.type := by
    simp only [Rules.addConstant, beq_self_eq_true, cond_true]
  have typedConst :=
    Derivable.const (Γ := .nil) declared formed W.universeOk
  rw [Tm.liftClosed_at_zero] at typedConst
  exact typedConst

end Witnessed

/-! ## Rigidity is necessary -/

/-- The root step from `c` to itself. Renaming and substitution fix a constant,
so the step is stable under both. -/
def loopComputation (c : DeclName) : RootComputation Head where
  step := fun l r => l = .const c ∧ r = .const c
  rename := by
    intro n m ρ l r h
    obtain ⟨hl, hr⟩ := h
    rw [hl, hr]
    exact ⟨rfl, rfl⟩
  substitute := by
    intro n m σ l r h
    obtain ⟨hl, hr⟩ := h
    rw [hl, hr]
    exact ⟨rfl, rfl⟩

/-- A package whose only root step is `c ⟶ c`. -/
def loopRules (c : DeclName) : Rules Head where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  computation := loopComputation c

/-- A term that steps to itself is not strongly normalizing. -/
theorem not_sn_of_self_step {R : Rules Head} {n : Nat} {t : Tm Head n}
    (step : StrongNormalization.Reduces R t t) : ¬ StrongNormalization.SN R t := by
  intro sn
  induction sn with
  | intro t _ ih => exact ih t step step

/-- A constant with the root step `c ⟶ c` has no normal form. -/
theorem loop_not_sn (c : DeclName) :
    ¬ StrongNormalization.SN (loopRules (Head := Head) c) (n := 0) (.const c) :=
  not_sn_of_self_step (.root ⟨rfl, rfl⟩)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
