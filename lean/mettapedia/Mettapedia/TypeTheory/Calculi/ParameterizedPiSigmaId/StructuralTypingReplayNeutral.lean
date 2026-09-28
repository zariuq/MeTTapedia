import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayGeneration

/-!
# Neutral subjects and structural replay type uniqueness

Without conversion, a neutral subject determines its displayed type apart from
cumulative changes between universe heads. In particular its Pi and Sigma
annotations are unique. This concerns supplied accepted replay trees, not
reconstruction of a certificate from erased syntax.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

variable {Head : Type}

/-- A variable or declared-constant elimination spine. Arguments need not be
normal; introductions and universe/type constructors are not neutral. -/
def Tm.neutral : {n : Nat} → Tm Head n → Bool
  | _, .var _ | _, .const _ => true
  | _, .app function _ => function.neutral
  | _, .fst p | _, .snd p => p.neutral
  | _, _ => false

theorem Tm.neutral_elimination_spine {n : Nat} (index : Fin n) (argument : Tm Head n) :
    (.snd (.fst (.app (.var index) argument)) : Tm Head n).neutral = true := rfl

theorem Tm.introduction_redex_not_neutral {n : Nat}
    (body : Tm Head (n + 1)) (argument : Tm Head n) :
    (.app (.lam body) argument : Tm Head n).neutral = false := rfl

namespace StructuralTypingReplay

/-- Neutral eliminations throughout the interpretation-relevant replay tree.
Formation evidence for lambdas is included because it supplies their domains.
Formation subtrees ignored by value assembly are not additional restrictions. -/
def Code.neutralEliminations {ConversionCode : Nat → Type} :
    {n : Nat} → Code Head ConversionCode n → Tm Head n → Tm Head n → Bool
  | _, .headType, _, _ | _, .var, _, _ | _, .const .., _, _ => true
  | _, .piForm u v domain body, .pi A B, _
  | _, .sigmaForm u v domain body, .sigma A B, _ =>
      domain.neutralEliminations A (.head u) && body.neutralEliminations B (.head v)
  | _, .lamIntro u formation body, .lam t, .pi A B =>
      formation.neutralEliminations (.pi A B) (.head u) && body.neutralEliminations t B
  | _, .appElim A B function argument, .app f a, _ =>
      f.neutral && function.neutralEliminations f (.pi A B) &&
        argument.neutralEliminations a A
  | _, .pairIntro _ _ first second, .pair x y, .sigma A B =>
      first.neutralEliminations x A && second.neutralEliminations y (inst0 x B)
  | _, .fstElim B pair, .fst p, type =>
      p.neutral && pair.neutralEliminations p (.sigma type B)
  | _, .sndElim A B pair, .snd p, _ =>
      p.neutral && pair.neutralEliminations p (.sigma A B)
  | _, .idForm _ _ left right, .id A x y, _ =>
      left.neutralEliminations x A && right.neutralEliminations y A
  | _, .reflIntro .., _, _ => true
  | _, .cumul u source, t, .head _ => source.neutralEliminations t (.head u)
  | _, _, _, _ => false

/-- The only possible discrepancy introduced by cumulative replay wrappers. -/
def EqualOrHeads {n : Nat} (first second : Tm Head n) : Prop :=
  first = second ∨ ∃ u v, first = .head u ∧ second = .head v

namespace EqualOrHeads

theorem refl {n : Nat} (type : Tm Head n) : EqualOrHeads type type := .inl rfl

theorem heads {n : Nat} (u v : Head) :
    EqualOrHeads (.head u : Tm Head n) (.head v) := .inr ⟨u, v, rfl, rfl⟩

theorem symm {n : Nat} {first second : Tm Head n}
    (related : EqualOrHeads first second) : EqualOrHeads second first := by
  rcases related with same | ⟨u, v, rfl, rfl⟩
  · exact .inl same.symm
  · exact heads v u

theorem trans {n : Nat} {first second third : Tm Head n}
    (left : EqualOrHeads first second) (right : EqualOrHeads second third) :
    EqualOrHeads first third := by
  rcases left with rfl | ⟨u, v, rfl, rfl⟩
  · exact right
  rcases right with rfl | ⟨_, w, _, rfl⟩
  · exact heads u v
  · exact heads u w

theorem eq_of_pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    {other : Tm Head n} (related : EqualOrHeads (.pi A B) other) : .pi A B = other := by
  rcases related with same | ⟨_, _, impossible, _⟩
  · exact same
  · cases impossible

theorem eq_of_sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    {other : Tm Head n} (related : EqualOrHeads (.sigma A B) other) : .sigma A B = other := by
  rcases related with same | ⟨_, _, impossible, _⟩
  · exact same
  · cases impossible

theorem pi_injective {n : Nat} {A C : Tm Head n} {B D : Tm Head (n + 1)}
    (related : EqualOrHeads (.pi A B) (.pi C D)) : A = C ∧ B = D :=
  Tm.pi.inj (eq_of_pi related)

theorem sigma_injective {n : Nat} {A C : Tm Head n} {B D : Tm Head (n + 1)}
    (related : EqualOrHeads (.sigma A B) (.sigma C D)) : A = C ∧ B = D :=
  Tm.sigma.inj (eq_of_sigma related)

end EqualOrHeads

/-- Removing cumulative wrappers changes only a universe head. The statement
uses the computed principal-view receipt and needs no typing uniqueness axiom. -/
theorem Code.principalView_equalOrHeads {n : Nat} (code : Code Head NoConversion n) :
    ∀ {displayed : Tm Head n} {view : PrincipalView Head NoConversion n},
      code.principalView displayed = some view → EqualOrHeads view.type displayed := by
  induction code with
  | cumul level source ih =>
      intro displayed view computed
      cases displayed <;> simp only [principalView] at computed <;> try contradiction
      rename_i head
      cases priorComputed : source.principalView (.head level) with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, Option.map_some, Option.some.injEq] at computed
          subst view
          exact (ih priorComputed).trans (EqualOrHeads.heads level head)
  | convert _ _ _ _ impossible _ _ => exact nomatch impossible
  | _ =>
      intro displayed view computed
      simp only [principalView, Option.some.injEq] at computed
      subst view
      exact EqualOrHeads.refl displayed

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]

theorem Code.principalView_noConversion_checked {n : Nat}
    (code : Code Head NoConversion n) {context : Ctx Head n} {subject displayed : Tm Head n}
    (accepted : check R noConversionCheck context subject displayed code = true) :
    ∃ view, code.principalView displayed = some view ∧
      check R noConversionCheck context subject view.type view.code = true ∧
      view.code.isPrincipal = true ∧ EqualOrHeads view.type displayed := by
  obtain ⟨view, computed, checked, _⟩ := code.principalView_checked R noConversionCheck accepted
  exact ⟨view, computed, checked, (code.principalView_reconstruct computed).2,
    code.principalView_equalOrHeads computed⟩

private theorem principal_var {n : Nat} {context : Ctx Head n} {index : Fin n}
    {type : Tm Head n} (code : Code Head NoConversion n)
    (principal : code.isPrincipal = true)
    (accepted : check R noConversionCheck context (.var index) type code = true) :
    type = context.lookup index := by
  cases code <;> simp_all [Code.isPrincipal, check]

private theorem principal_const {n : Nat} {context : Ctx Head n} {name : DeclName}
    {type : Tm Head n} (code : Code Head NoConversion n)
    (principal : code.isPrincipal = true)
    (accepted : check R noConversionCheck context (.const name) type code = true) :
    ∃ declared, R.constantType name = some declared ∧ type = liftClosed declared := by
  cases code <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  cases known : R.constantType name with
  | none => simp [check, known] at accepted
  | some declared =>
      simp only [check, known, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨declared, rfl, accepted.2⟩

private theorem principal_app {n : Nat} {context : Ctx Head n} {f a type : Tm Head n}
    (code : Code Head NoConversion n) (principal : code.isPrincipal = true)
    (accepted : check R noConversionCheck context (.app f a) type code = true) :
    ∃ A B function argument,
      check R noConversionCheck context f (.pi A B) function = true ∧
      check R noConversionCheck context a A argument = true ∧ type = inst0 a B := by
  cases code <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨_, _, _, _, accepted.1.1, accepted.1.2, accepted.2⟩

private theorem principal_fst {n : Nat} {context : Ctx Head n} {p type : Tm Head n}
    (code : Code Head NoConversion n) (principal : code.isPrincipal = true)
    (accepted : check R noConversionCheck context (.fst p) type code = true) :
    ∃ B pair, check R noConversionCheck context p (.sigma type B) pair = true := by
  cases code <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  exact ⟨_, _, accepted⟩

private theorem principal_snd {n : Nat} {context : Ctx Head n} {p type : Tm Head n}
    (code : Code Head NoConversion n) (principal : code.isPrincipal = true)
    (accepted : check R noConversionCheck context (.snd p) type code = true) :
    ∃ A B pair, check R noConversionCheck context p (.sigma A B) pair = true ∧
      type = inst0 (.fst p) B := by
  cases code <;> simp only [Code.isPrincipal, Bool.false_eq_true] at principal
  all_goals try { simp [check] at accepted }
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨_, _, _, accepted.1, accepted.2⟩

/-- Accepted typings of the same neutral raw subject have the same type,
except for changes between universe heads. No condition on head typing,
context formation, or semantic environments is needed. -/
theorem neutral_type_equalOrHeads {n : Nat} (subject : Tm Head n) :
    ∀ {context : Ctx Head n} {firstType secondType : Tm Head n}
      (first second : Code Head NoConversion n), subject.neutral = true →
      check R noConversionCheck context subject firstType first = true →
      check R noConversionCheck context subject secondType second = true →
      EqualOrHeads firstType secondType := by
  induction subject with
  | head _ | pi _ _ _ _ | sigma _ _ _ _ | lam _ _ | pair _ _ _ _ | id _ _ _ _ _ _ | refl _ _ =>
      intro context firstType secondType first second neutral
      exact False.elim (Bool.noConfusion neutral)
  | var index =>
      intro context firstType secondType first second _ firstChecked secondChecked
      obtain ⟨left, _, leftChecked, leftPrincipal, leftRelated⟩ :=
        first.principalView_noConversion_checked R firstChecked
      obtain ⟨right, _, rightChecked, rightPrincipal, rightRelated⟩ :=
        second.principalView_noConversion_checked R secondChecked
      have same : left.type = right.type :=
        (principal_var R left.code leftPrincipal leftChecked).trans
          (principal_var R right.code rightPrincipal rightChecked).symm
      exact leftRelated.symm.trans (EqualOrHeads.trans (Or.inl same) rightRelated)
  | const name =>
      intro context firstType secondType first second _ firstChecked secondChecked
      obtain ⟨left, _, leftChecked, leftPrincipal, leftRelated⟩ :=
        first.principalView_noConversion_checked R firstChecked
      obtain ⟨right, _, rightChecked, rightPrincipal, rightRelated⟩ :=
        second.principalView_noConversion_checked R secondChecked
      obtain ⟨leftDeclared, leftKnown, leftType⟩ := principal_const R left.code leftPrincipal leftChecked
      obtain ⟨rightDeclared, rightKnown, rightType⟩ := principal_const R right.code rightPrincipal rightChecked
      have sameDeclared := Option.some.inj (leftKnown.symm.trans rightKnown)
      subst rightDeclared
      exact leftRelated.symm.trans (EqualOrHeads.trans (Or.inl (leftType.trans rightType.symm)) rightRelated)
  | app f a ihF _ =>
      intro context firstType secondType first second neutral firstChecked secondChecked
      obtain ⟨left, _, leftChecked, leftPrincipal, leftRelated⟩ :=
        first.principalView_noConversion_checked R firstChecked
      obtain ⟨right, _, rightChecked, rightPrincipal, rightRelated⟩ :=
        second.principalView_noConversion_checked R secondChecked
      obtain ⟨A, B, function, _, functionChecked, _, leftType⟩ :=
        principal_app R left.code leftPrincipal leftChecked
      obtain ⟨C, D, otherFunction, _, otherChecked, _, rightType⟩ :=
        principal_app R right.code rightPrincipal rightChecked
      obtain ⟨_, sameBody⟩ :=
        (ihF function otherFunction neutral functionChecked otherChecked).pi_injective
      subst D
      exact leftRelated.symm.trans (EqualOrHeads.trans (Or.inl (leftType.trans rightType.symm)) rightRelated)
  | fst p ih =>
      intro context firstType secondType first second neutral firstChecked secondChecked
      obtain ⟨left, _, leftChecked, leftPrincipal, leftRelated⟩ :=
        first.principalView_noConversion_checked R firstChecked
      obtain ⟨right, _, rightChecked, rightPrincipal, rightRelated⟩ :=
        second.principalView_noConversion_checked R secondChecked
      obtain ⟨B, pair, pairChecked⟩ := principal_fst R left.code leftPrincipal leftChecked
      obtain ⟨D, otherPair, otherChecked⟩ := principal_fst R right.code rightPrincipal rightChecked
      have same := (ih pair otherPair neutral pairChecked otherChecked).sigma_injective
      exact leftRelated.symm.trans (EqualOrHeads.trans (Or.inl same.1) rightRelated)
  | snd p ih =>
      intro context firstType secondType first second neutral firstChecked secondChecked
      obtain ⟨left, _, leftChecked, leftPrincipal, leftRelated⟩ :=
        first.principalView_noConversion_checked R firstChecked
      obtain ⟨right, _, rightChecked, rightPrincipal, rightRelated⟩ :=
        second.principalView_noConversion_checked R secondChecked
      obtain ⟨A, B, pair, pairChecked, leftType⟩ := principal_snd R left.code leftPrincipal leftChecked
      obtain ⟨C, D, otherPair, otherChecked, rightType⟩ := principal_snd R right.code rightPrincipal rightChecked
      obtain ⟨_, sameBody⟩ := (ih pair otherPair neutral pairChecked otherChecked).sigma_injective
      subst D
      exact leftRelated.symm.trans (EqualOrHeads.trans (Or.inl (leftType.trans rightType.symm)) rightRelated)

theorem neutral_pi_type_unique {n : Nat} {context : Ctx Head n}
    {subject A C : Tm Head n} {B D : Tm Head (n + 1)}
    (first second : Code Head NoConversion n) (neutral : subject.neutral = true)
    (firstChecked : check R noConversionCheck context subject (.pi A B) first = true)
    (secondChecked : check R noConversionCheck context subject (.pi C D) second = true) :
    A = C ∧ B = D :=
  (neutral_type_equalOrHeads R subject first second neutral firstChecked secondChecked).pi_injective

theorem neutral_sigma_type_unique {n : Nat} {context : Ctx Head n}
    {subject A C : Tm Head n} {B D : Tm Head (n + 1)}
    (first second : Code Head NoConversion n) (neutral : subject.neutral = true)
    (firstChecked : check R noConversionCheck context subject (.sigma A B) first = true)
    (secondChecked : check R noConversionCheck context subject (.sigma C D) second = true) :
    A = C ∧ B = D :=
  (neutral_type_equalOrHeads R subject first second neutral firstChecked secondChecked).sigma_injective

#print axioms Tm.neutral_elimination_spine
#print axioms Tm.introduction_redex_not_neutral
#print axioms Code.principalView_equalOrHeads
#print axioms neutral_type_equalOrHeads
#print axioms neutral_pi_type_unique
#print axioms neutral_sigma_type_unique

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
