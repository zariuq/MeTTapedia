import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis

/-!
# Deciding whether a type is usable at another

Between two types of a formed context, cumulative subtyping is decided once the
rule package decides its head equality and its universe order. The decision
reads the left type in weak-head normal form and compares by its former:

* a universe is usable exactly at the universes above it;
* a dependent function type exactly at dependent function types with an equal
  domain and a codomain above its own, over its own domain;
* a dependent pair type exactly at dependent pair types whose domain is above
  its domain and whose codomain is above its codomain, over its own domain;
* any other type exactly at the types equal to it.

Each clause is a characterization theorem below. The recursion follows the
algorithmic derivation of the left type's reflexivity, which exists by
completeness, so it terminates wherever the equality algorithm does.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## The clauses of the decision -/

section Clauses

variable (facts : FormFacts S.R S.roles)
include facts

/-- A universe is usable exactly at the universes above it. -/
theorem Below.universe_iff (algebra : CumulativeAlgebra S.R) {n : Nat} {Γ : Ctx Head n}
    {u : Head} {T : Tm Head n} (formed : CtxFormed S.R Γ) (hu : S.R.isUniverse u) :
    Below S.R Γ (.head u) T ↔
      ∃ v, S.R.isUniverse v ∧ TypeEq S.R Γ T (.head v) ∧ S.R.cumulative u v := by
  constructor
  · intro le
    exact Below.universe_cumulative facts algebra le formed hu
      (IsType.refl (IsType.head_of_universe hu))
  · rintro ⟨v, _, eT, c⟩
    exact .subTrans (.subUniv c) (TypeEq.below (TypeEq.symm eT))

/-- A dependent function type is usable exactly at dependent function types with
an equal domain and a codomain above its own, over its own domain. -/
theorem Below.pi_iff {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {T : Tm Head n} (formed : CtxFormed S.R Γ) (typePi : IsType S.R Γ (.pi A B)) :
    Below S.R Γ (.pi A B) T ↔
      ∃ A' B', TypeEq S.R Γ T (.pi A' B') ∧ TypeEq S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B' := by
  constructor
  · intro le
    exact Below.pi_source facts le formed (IsType.refl typePi)
  · rintro ⟨A', B', eT, ⟨w, hw, eA⟩, leB⟩
    obtain ⟨u, hu, tPi⟩ := typePi
    obtain ⟨u', hu', tPi'⟩ := (TypeEq.isType eT formed).2
    exact .subTrans (.subPi tPi hu tPi' hu' eA hw leB) (TypeEq.below (TypeEq.symm eT))

/-- A dependent pair type is usable exactly at dependent pair types whose domain
is above its domain and whose codomain is above its codomain, over its own
domain. -/
theorem Below.sigma_iff {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {T : Tm Head n} (formed : CtxFormed S.R Γ) (typeSigma : IsType S.R Γ (.sigma A B)) :
    Below S.R Γ (.sigma A B) T ↔
      ∃ A' B', TypeEq S.R Γ T (.sigma A' B') ∧ Below S.R Γ A A' ∧
        Below S.R (.snoc Γ A) B B' := by
  constructor
  · intro le
    exact Below.sigma_source facts le formed (IsType.refl typeSigma)
  · rintro ⟨A', B', eT, leA, leB⟩
    obtain ⟨u, hu, tSigma⟩ := typeSigma
    obtain ⟨u', hu', tSigma'⟩ := (TypeEq.isType eT formed).2
    exact .subTrans (.subSigma tSigma hu tSigma' hu' leA leB) (TypeEq.below (TypeEq.symm eT))

/-- A type of rigid shape is usable exactly at the types equal to it. -/
theorem RigidShape.below_iff {n : Nat} {Γ : Ctx Head n} {A T : Tm Head n}
    (shape : RigidShape S.R S.roles Γ A) (formed : CtxFormed S.R Γ) :
    Below S.R Γ A T ↔ TypeEq S.R Γ A T :=
  ⟨fun le => RigidShape.rigid facts shape formed le, TypeEq.below⟩

/-- A type is a dependent function type in weak-head normal form, or equal to
none. -/
theorem IsType.pi_or {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} (formed : CtxFormed S.R Γ)
    (isX : IsType S.R Γ X) :
    (∃ A B, RedTy S.R S.roles Γ X (.pi A B)) ∨ ∀ A B, ¬ TypeEq S.R Γ X (.pi A B) := by
  obtain ⟨X', red, form⟩ := facts.typeForm isX formed
  have toForm : ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, TypeEq S.R Γ X (.pi A B) →
      ∃ A' B', X' = .pi A' B' := fun e => by
    obtain ⟨A', B', same, _, _⟩ := (facts.forms
      (TypeEq.trans S.levels (TypeEq.symm e) red.typeEq) formed (.inr (.inl ⟨_, _, rfl⟩))
      form).pi_left
    exact ⟨A', B', same⟩
  rcases form with ⟨_, rfl⟩ | ⟨A, B, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | neutral |
    ⟨_, _, _, rfl⟩
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inl ⟨A, B, red⟩
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ e => by
      obtain ⟨_, _, same⟩ := toForm e
      exact neutral.not_former.2.1 _ _ same
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same

/-- A type is a dependent pair type in weak-head normal form, or equal to none. -/
theorem IsType.sigma_or {n : Nat} {Γ : Ctx Head n} {X : Tm Head n} (formed : CtxFormed S.R Γ)
    (isX : IsType S.R Γ X) :
    (∃ A B, RedTy S.R S.roles Γ X (.sigma A B)) ∨ ∀ A B, ¬ TypeEq S.R Γ X (.sigma A B) := by
  obtain ⟨X', red, form⟩ := facts.typeForm isX formed
  have toForm : ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, TypeEq S.R Γ X (.sigma A B) →
      ∃ A' B', X' = .sigma A' B' := fun e => by
    obtain ⟨A', B', same, _, _⟩ := (facts.forms
      (TypeEq.trans S.levels (TypeEq.symm e) red.typeEq) formed
      (.inr (.inr (.inl ⟨_, _, rfl⟩))) form).sigma_left
    exact ⟨A', B', same⟩
  rcases form with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨A, B, rfl⟩ | ⟨_, _, _, rfl⟩ | neutral |
    ⟨_, _, _, rfl⟩
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inl ⟨A, B, red⟩
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same
  · exact .inr fun _ _ e => by
      obtain ⟨_, _, same⟩ := toForm e
      exact neutral.not_former.2.2.1 _ _ same
  · exact .inr fun _ _ e => by obtain ⟨_, _, same⟩ := toForm e; cases same

end Clauses

/-! ## The decision -/

/-- What a derivation of the algorithmic equality of types decides: whether its
left type is usable at any other type of the context. -/
def DecidesBelow (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A _ => CtxFormed S.R Γ → IsType S.R Γ A → ∀ {B}, IsType S.R Γ B →
      Below S.R Γ A B ∨ ¬ Below S.R Γ A B
  | .typesW Γ A _ => CtxFormed S.R Γ → IsType S.R Γ A → ∀ {B}, IsType S.R Γ B →
      Below S.R Γ A B ∨ ¬ Below S.R Γ A B
  | _ => True

section Decision

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (decideHeads : ∀ h h' : Head, HeadSame S.R h h' ∨ ¬ HeadSame S.R h h')
  (complete : AlgorithmicComplete S.R S.roles)
  (decideCumulative : ∀ u v : Head, S.R.cumulative u v ∨ ¬ S.R.cumulative u v)
include facts roots heads algebra decideHeads complete decideCumulative

omit decideCumulative in
/-- A type of rigid shape is usable at another type exactly when they are equal,
which is decided. -/
theorem RigidShape.decide_below {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (shape : RigidShape S.R S.roles Γ A) (formed : CtxFormed S.R Γ) (typeA : IsType S.R Γ A)
    (typeB : IsType S.R Γ B) : Below S.R Γ A B ∨ ¬ Below S.R Γ A B := by
  rcases TypeEq.decide facts roots heads algebra decideHeads complete formed typeA
      typeB with e | ne
  · exact .inl (TypeEq.below e)
  · exact .inr fun le => ne ((RigidShape.below_iff facts shape formed).1 le)

/-- Every derivation of the algorithmic equality of types decides whether its
left type is usable at any other type. -/
theorem Algorithmic.decidesBelow {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : DecidesBelow S st := by
  induction derivation with
  | types rA _ _ _ _ ih =>
      intro formed _ B typeB
      rcases ih formed rA.targetType typeB with yes | no
      · exact .inl (.subTrans (TypeEq.below rA.typeEq) yes)
      · exact .inr fun le => no (.subTrans (TypeEq.below (TypeEq.symm rA.typeEq)) le)
  | @heads n Γ h h' u _ _ _ _ =>
      intro formed typeA B typeB
      rcases S.levels.universe_decided h with hh | nh
      · rcases IsType.universe_or facts formed typeB with ⟨v, hv, eB⟩ | notUniverse
        · rcases decideCumulative h v with c | nc
          · exact .inl ((Below.universe_iff facts algebra formed hh).2 ⟨v, hv, eB, c⟩)
          · refine .inr fun le => nc ?_
            obtain ⟨v', _, eB', c'⟩ := (Below.universe_iff facts algebra formed hh).1 le
            exact algebra.same_right c' (TypeEq.head_injective facts
              (TypeEq.trans S.levels (TypeEq.symm eB') eB) formed)
        · refine .inr fun le => ?_
          obtain ⟨v', hv', eB', _⟩ := (Below.universe_iff facts algebra formed hh).1 le
          exact notUniverse v' eB' hv'
      · exact RigidShape.decide_below facts roots heads algebra decideHeads complete
          (.head nh) formed typeA typeB
  | @pi n Γ A A' B B' isA _ _ _ ihB =>
      intro formed typePi T typeT
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed isA
      obtain ⟨_, ⟨_, hB, tB⟩⟩ := IsType.pi_parts typePi
      have clause := Below.pi_iff facts (T := T) formed typePi
      rcases IsType.pi_or facts formed typeT with ⟨A₁, B₁, red⟩ | notPi
      · have eT := red.typeEq
        obtain ⟨⟨_, hA₁, tA₁⟩, ⟨_, hB₁, tB₁⟩⟩ := IsType.pi_parts red.targetType
        rcases TypeEq.decide facts roots heads algebra decideHeads complete formed isA
            ⟨_, hA₁, tA₁⟩ with eA | neA
        · rcases ihB formedA ⟨_, hB, tB⟩ (B := B₁)
              ⟨_, hB₁, Typed.ctxBelow tB₁ (TypeEq.below eA)⟩ with yes | no
          · exact .inl (clause.2 ⟨A₁, B₁, eT, eA, yes⟩)
          · refine .inr fun le => no ?_
            obtain ⟨_, _, eT', _, leB⟩ := clause.1 le
            obtain ⟨_, eB⟩ := TypeEq.pi_injective facts
              (TypeEq.trans S.levels (TypeEq.symm eT) eT') formed
            exact .subTrans leB (Below.ctxConv (TypeEq.below (TypeEq.symm eB)) (TypeEq.symm eA))
        · refine .inr fun le => neA ?_
          obtain ⟨_, _, eT', eA', _⟩ := clause.1 le
          obtain ⟨e₁₂, _⟩ := TypeEq.pi_injective facts
            (TypeEq.trans S.levels (TypeEq.symm eT) eT') formed
          exact TypeEq.trans S.levels eA' (TypeEq.symm e₁₂)
      · refine .inr fun le => ?_
        obtain ⟨A₂, B₂, eT', _, _⟩ := clause.1 le
        exact notPi A₂ B₂ eT'
  | @sigma n Γ A A' B B' isA _ _ ihA ihB =>
      intro formed typeSigma T typeT
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed isA
      obtain ⟨_, ⟨_, hB, tB⟩⟩ := IsType.sigma_parts typeSigma
      have clause := Below.sigma_iff facts (T := T) formed typeSigma
      rcases IsType.sigma_or facts formed typeT with ⟨A₁, B₁, red⟩ | notSigma
      · have eT := red.typeEq
        obtain ⟨⟨_, hA₁, tA₁⟩, ⟨_, hB₁, tB₁⟩⟩ := IsType.sigma_parts red.targetType
        rcases ihA formed isA (B := A₁) ⟨_, hA₁, tA₁⟩ with leA | nleA
        · rcases ihB formedA ⟨_, hB, tB⟩ (B := B₁) ⟨_, hB₁, Typed.ctxBelow tB₁ leA⟩ with
            yes | no
          · exact .inl (clause.2 ⟨A₁, B₁, eT, leA, yes⟩)
          · refine .inr fun le => no ?_
            obtain ⟨_, _, eT', _, leB⟩ := clause.1 le
            obtain ⟨_, eB⟩ := TypeEq.sigma_injective facts
              (TypeEq.trans S.levels (TypeEq.symm eT) eT') formed
            exact .subTrans leB (Below.ctxBelow (TypeEq.below (TypeEq.symm eB)) leA)
        · refine .inr fun le => nleA ?_
          obtain ⟨_, _, eT', leA', _⟩ := clause.1 le
          obtain ⟨e₁₂, _⟩ := TypeEq.sigma_injective facts
            (TypeEq.trans S.levels (TypeEq.symm eT) eT') formed
          exact .subTrans leA' (TypeEq.below (TypeEq.symm e₁₂))
      · refine .inr fun le => ?_
        obtain ⟨A₂, B₂, eT', _, _⟩ := clause.1 le
        exact notSigma A₂ B₂ eT'
  | id _ _ _ _ _ _ =>
      intro formed typeA B typeB
      exact RigidShape.decide_below facts roots heads algebra decideHeads complete
        .id formed typeA typeB
  | inductiveType role _ =>
      intro formed typeA B typeB
      exact RigidShape.decide_below facts roots heads algebra decideHeads complete
        (.inductiveType role) formed typeA typeB
  | neutralTypes nA _ _ _ _ =>
      intro formed typeA B typeB
      exact RigidShape.decide_below facts roots heads algebra decideHeads complete
        (.neutral nA) formed typeA typeB
  | terms => trivial
  | univ => trivial
  | eta => trivial
  | sigmaEta => trivial
  | refl => trivial
  | spine => trivial
  | var => trivial
  | const => trivial
  | app => trivial
  | fst => trivial
  | snd => trivial
  | spinesW => trivial

/-- Whether a type of a formed context is usable at another is decided. -/
theorem Below.decide {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (typeA : IsType S.R Γ A) (typeB : IsType S.R Γ B) :
    Below S.R Γ A B ∨ ¬ Below S.R Γ A B :=
  Algorithmic.decidesBelow facts roots heads algebra decideHeads complete
    decideCumulative (complete.types typeA.refl formed) formed typeA typeB

end Decision

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
