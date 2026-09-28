import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness

/-!
# Decidability of the algorithmic equality

The comparison of two typed terms terminates. By completeness each of them is
algorithmically equal to itself, and the comparison of the two follows the
derivation for the left one: weak-head normal forms are unique, the type
chooses the comparison, a spine determines the type its arguments are
compared at, and the right term's own derivation supplies what the comparison
needs of it. Where the right term has another shape or another head, no
derivation exists. So between two terms of a type in a formed context the
algorithmic equality is decided, and with it the typed equality, once the rule
package's head equality is decided.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## The type a spine is compared at -/

/-- The type at which a spine is compared in weak-head normal form is
determined by the spine, when the type before normalization is. -/
theorem Algorithmic.spinesW_determined {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    (determined : ∀ {u u' U U' : Tm Head n}, Algorithmic S.R S.roles (.spines Γ t u U) →
      Algorithmic S.R S.roles (.spines Γ t u' U') → U = U')
    {u u' U U' : Tm Head n} (first : Algorithmic S.R S.roles (.spinesW Γ t u U))
    (second : Algorithmic S.R S.roles (.spinesW Γ t u' U')) : U = U' := by
  cases first with
  | spinesW d r f =>
  cases second with
  | spinesW d' r' f' =>
  obtain rfl := determined d d'
  exact RedTy.unique r r' f.whnf f'.whnf

/-- The type at which a spine is compared is determined by the spine: its
head's type, instantiated at its arguments. -/
theorem Algorithmic.spines_determined {n : Nat} {Γ : Ctx Head n} (t : Tm Head n) :
    ∀ {u u' U U' : Tm Head n}, Algorithmic S.R S.roles (.spines Γ t u U) →
      Algorithmic S.R S.roles (.spines Γ t u' U') → U = U' := by
  induction t with
  | var i =>
      intro u u' U U' first second
      cases first
      cases second
      rfl
  | const c =>
      intro u u' U U' first second
      cases first with
      | const declared _ =>
      cases second with
      | const declared' _ =>
      rw [declared] at declared'
      cases declared'
      rfl
  | app f a ihf _ =>
      intro u u' U U' first second
      cases first with
      | app df _ =>
      cases second with
      | app df' _ =>
      cases Algorithmic.spinesW_determined ihf df df'
      rfl
  | fst p ih =>
      intro u u' U U' first second
      cases first with
      | fst dp =>
      cases second with
      | fst dp' =>
      cases Algorithmic.spinesW_determined ih dp dp'
      rfl
  | snd p ih =>
      intro u u' U U' first second
      cases first with
      | snd dp =>
      cases second with
      | snd dp' =>
      cases Algorithmic.spinesW_determined ih dp dp'
      rfl
  | head => intro u u' U U' first; cases first
  | pi => intro u u' U U' first; cases first
  | sigma => intro u u' U U' first; cases first
  | id => intro u u' U U' first; cases first
  | lam => intro u u' U U' first; cases first
  | pair => intro u u' U U' first; cases first
  | refl => intro u u' U U' first; cases first

/-! ## The decision -/

/-- What a derivation decides: the comparison of its left side with the left
side of any derivation of the same judgment. A spine is decided together with
the type it is compared at. -/
def Decides (S : Setting Head L) : AlgorithmicStatement Head → Prop
  | .types Γ A _ => CtxFormed S.R Γ → ∀ {B B'}, Algorithmic S.R S.roles (.types Γ B B') →
      Algorithmic S.R S.roles (.types Γ A B) ∨ ¬ Algorithmic S.R S.roles (.types Γ A B)
  | .typesW Γ A _ => CtxFormed S.R Γ → ∀ {B B'}, Algorithmic S.R S.roles (.typesW Γ B B') →
      Algorithmic S.R S.roles (.typesW Γ A B) ∨ ¬ Algorithmic S.R S.roles (.typesW Γ A B)
  | .terms Γ t _ A => CtxFormed S.R Γ → ∀ {u u'}, Algorithmic S.R S.roles (.terms Γ u u' A) →
      Algorithmic S.R S.roles (.terms Γ t u A) ∨ ¬ Algorithmic S.R S.roles (.terms Γ t u A)
  | .termsW Γ t _ A => CtxFormed S.R Γ → ∀ {u u'},
      Algorithmic S.R S.roles (.termsW Γ u u' A) →
      Algorithmic S.R S.roles (.termsW Γ t u A) ∨ ¬ Algorithmic S.R S.roles (.termsW Γ t u A)
  | .spines Γ t _ _ => CtxFormed S.R Γ → ∀ {u u' U'},
      Algorithmic S.R S.roles (.spines Γ u u' U') →
      (∃ U, Algorithmic S.R S.roles (.spines Γ t u U)) ∨
        ¬ ∃ U, Algorithmic S.R S.roles (.spines Γ t u U)
  | .spinesW Γ t _ U => CtxFormed S.R Γ → ∀ {u u' U'},
      Algorithmic S.R S.roles (.spinesW Γ u u' U') →
      Algorithmic S.R S.roles (.spinesW Γ t u U) ∨ ¬ Algorithmic S.R S.roles (.spinesW Γ t u U)

section Decidability

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (decideHeads : ∀ h h' : Head, HeadSame S.R h h' ∨ ¬ HeadSame S.R h h')
include facts roots heads algebra decideHeads

/-- Every derivation decides the comparison of its left side. -/
theorem Algorithmic.decides {st : AlgorithmicStatement Head}
    (derivation : Algorithmic S.R S.roles st) : Decides S st := by
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  have sound := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.sound facts roots heads algebra d
  induction derivation with
  | types rA _ fA _ _ ih =>
      intro formed B B' second
      cases second with
      | types rB _ fB _ d₂ =>
          rcases ih formed d₂ with yes | no
          · exact .inl (.types rA rB fA fB yes)
          · right
            intro h
            cases h with
            | types rA₃ rB₃ fA₃ fB₃ d₃ =>
                obtain rfl := RedTy.unique rA rA₃ fA.whnf fA₃.whnf
                obtain rfl := RedTy.unique rB rB₃ fB.whnf fB₃.whnf
                exact no d₃
  | heads _ tA _ hu =>
      intro formed B B' second
      cases second with
      | heads _ tC _ hu₂ =>
          rcases decideHeads _ _ with yes | no
          · obtain ⟨w, join⟩ := S.levels.join_exists hu hu₂
            obtain ⟨cu, cv⟩ := S.levels.join_upper join
            exact .inl (.heads yes (.cumul tA cu) (.cumul tC cv) (S.levels.join_level join).1)
          · right
            intro h
            cases h with
            | heads same _ _ _ => exact no same
            | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
      | pi =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
      | sigma =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
      | id =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
      | inductiveType =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
      | neutralTypes nB _ _ _ =>
          right
          intro h
          cases h with
          | heads => exact absurd rfl (nB.not_former.1 _)
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.1 _)
  | pi isA _ _ ihA ihB =>
      intro formed C C' second
      cases second with
      | pi _ dA₂ dB₂ =>
          rcases ihA formed dA₂ with yesA | noA
          · have eA : TypeEq S.R _ _ _ := sound yesA formed
            have formedA : CtxFormed S.R (.snoc _ _) := .snoc formed isA
            rcases ihB formedA (conv dB₂ (.snoc (CtxEq.refl _ formed) eA) formedA) with
              yesB | noB
            · exact .inl (.pi isA yesA yesB)
            · right
              intro h
              cases h with
              | pi _ _ dB₃ => exact noB dB₃
              | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
          · right
            intro h
            cases h with
            | pi _ dA₃ _ => exact noA dA₃
            | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
      | heads =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
      | sigma =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
      | id =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
      | inductiveType =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
      | neutralTypes nC _ _ _ =>
          right
          intro h
          cases h with
          | pi => exact absurd rfl (nC.not_former.2.1 _ _)
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.1 _ _)
  | sigma isA _ _ ihA ihB =>
      intro formed C C' second
      cases second with
      | sigma _ dA₂ dB₂ =>
          rcases ihA formed dA₂ with yesA | noA
          · have eA : TypeEq S.R _ _ _ := sound yesA formed
            have formedA : CtxFormed S.R (.snoc _ _) := .snoc formed isA
            rcases ihB formedA (conv dB₂ (.snoc (CtxEq.refl _ formed) eA) formedA) with
              yesB | noB
            · exact .inl (.sigma isA yesA yesB)
            · right
              intro h
              cases h with
              | sigma _ _ dB₃ => exact noB dB₃
              | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
          · right
            intro h
            cases h with
            | sigma _ dA₃ _ => exact noA dA₃
            | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
      | heads =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
      | pi =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
      | id =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
      | inductiveType =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
      | neutralTypes nC _ _ _ =>
          right
          intro h
          cases h with
          | sigma => exact absurd rfl (nC.not_former.2.2.1 _ _)
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.1 _ _)
  | id _ _ _ ihA ihx ihy =>
      intro formed C C' second
      cases second with
      | id dA₂ dx₂ dy₂ =>
          rcases ihA formed dA₂ with yesA | noA
          · have eA : TypeEq S.R _ _ _ := sound yesA formed
            rcases ihx formed (conv dx₂ (CtxEq.refl _ formed) formed eA.symm) with yesx | nox
            · rcases ihy formed (conv dy₂ (CtxEq.refl _ formed) formed eA.symm) with yesy | noy
              · exact .inl (.id yesA yesx yesy)
              · right
                intro h
                cases h with
                | id _ _ dy₃ => exact noy dy₃
                | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
            · right
              intro h
              cases h with
              | id _ dx₃ _ => exact nox dx₃
              | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
          · right
            intro h
            cases h with
            | id dA₃ _ _ => exact noA dA₃
            | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
      | heads =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
      | pi =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
      | sigma =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
      | inductiveType =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
      | neutralTypes nC _ _ _ =>
          right
          intro h
          cases h with
          | id => exact absurd rfl (nC.not_former.2.2.2 _ _ _)
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
  | @inductiveType n Γ T ctors role isT =>
      intro formed C C' second
      cases second with
      | @inductiveType _ _ T₂ _ _ _ =>
          rcases Decidable.em (T = T₂) with same | different
          · subst same
            exact .inl (.inductiveType role isT)
          · right
            intro h
            cases h with
            | inductiveType => exact different rfl
            | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
      | heads =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
      | pi =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
      | sigma =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
      | id =>
          right
          intro h
          cases h with
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
      | neutralTypes nC _ _ _ =>
          right
          intro h
          cases h with
          | inductiveType => exact absurd rfl (nC.ne_inductive role)
          | neutralTypes nA _ _ _ => exact absurd rfl (nA.ne_inductive role)
  | @neutralTypes n Γ A A' u nA _ hu d ih =>
      intro formed C C' second
      cases second with
      | neutralTypes nC _ _ d₂ =>
          rcases ih formed d₂ with yes | no
          · exact .inl (.neutralTypes nA nC hu yes)
          · right
            intro h
            cases h with
            | heads => exact absurd rfl (nA.not_former.1 _)
            | pi => exact absurd rfl (nA.not_former.2.1 _ _)
            | sigma => exact absurd rfl (nA.not_former.2.2.1 _ _)
            | id => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
            | inductiveType role _ => exact absurd rfl (nA.ne_inductive role)
            | neutralTypes _ _ _ d₃ =>
                cases Algorithmic.spinesW_determined (Algorithmic.spines_determined A) d₃ d
                exact no d₃
      | heads =>
          right
          intro h
          cases h with
          | heads => exact absurd rfl (nA.not_former.1 _)
          | neutralTypes _ nC _ _ => exact absurd rfl (nC.not_former.1 _)
      | pi =>
          right
          intro h
          cases h with
          | pi => exact absurd rfl (nA.not_former.2.1 _ _)
          | neutralTypes _ nC _ _ => exact absurd rfl (nC.not_former.2.1 _ _)
      | sigma =>
          right
          intro h
          cases h with
          | sigma => exact absurd rfl (nA.not_former.2.2.1 _ _)
          | neutralTypes _ nC _ _ => exact absurd rfl (nC.not_former.2.2.1 _ _)
      | id =>
          right
          intro h
          cases h with
          | id => exact absurd rfl (nA.not_former.2.2.2 _ _ _)
          | neutralTypes _ nC _ _ => exact absurd rfl (nC.not_former.2.2.2 _ _ _)
      | inductiveType role _ =>
          right
          intro h
          cases h with
          | inductiveType => exact absurd rfl (nA.ne_inductive role)
          | neutralTypes _ nC _ _ => exact absurd rfl (nC.ne_inductive role)
  | terms rA fA rt _ d ih =>
      intro formed u u' second
      cases second with
      | terms rA₂ fA₂ ru _ d₂ =>
          obtain rfl := RedTy.unique rA rA₂ fA.whnf fA₂.whnf
          rcases ih formed d₂ with yes | no
          · exact .inl (.terms rA fA rt ru yes)
          · right
            intro h
            cases h with
            | terms rA₃ fA₃ rt₃ ru₃ d₃ =>
                obtain rfl := RedTy.unique rA rA₃ fA.whnf fA₃.whnf
                obtain rfl := RedTm.whnf_unique rt rt₃ d.termsW_whnf.1 d₃.termsW_whnf.1
                obtain rfl := RedTm.whnf_unique ru ru₃ d₂.termsW_whnf.1 d₃.termsW_whnf.2
                exact no d₃
  | univ hu tt _ _ ih =>
      intro formed u u' second
      cases second with
      | univ _ tu _ d₂ =>
          rcases ih formed d₂ with yes | no
          · exact .inl (.univ hu tt tu yes)
          · right
            intro h
            cases h with
            | univ _ _ _ d₃ => exact no d₃
            | spine sA _ _ _ _ _ => exact absurd hu sA.not_universe
      | spine sA _ _ _ _ _ => exact absurd hu sA.not_universe
  | eta isA tf funF _ _ _ ih =>
      intro formed u u' second
      cases second with
      | eta _ tg funG _ _ d₂ =>
          rcases ih (.snoc formed isA) d₂ with yes | no
          · exact .inl (.eta isA tf funF tg funG yes)
          · right
            intro h
            cases h with
            | eta _ _ _ _ _ d₃ => exact no d₃
            | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_pi
      | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_pi
  | sigmaEta tp pairP _ _ _ _ ih₁ ih₂ =>
      intro formed u u' second
      cases second with
      | sigmaEta tq pairQ _ _ e₁ e₂ =>
          rcases ih₁ formed e₁ with yes₁ | no₁
          · have eFst : Equal S.R _ _ _ _ := sound yes₁ formed
            obtain ⟨s, hs, tSigma⟩ := Typed.isType tp formed
            obtain ⟨_, ⟨w, hw, tB⟩⟩ := IsType.sigma_parts ⟨s, hs, tSigma⟩
            have eSnd := TypeEq.of_instantiateEq tB hw (.fstElim tq) (.symm eFst)
            rcases ih₂ formed (conv e₂ (CtxEq.refl _ formed) formed eSnd) with yes₂ | no₂
            · exact .inl (.sigmaEta tp pairP tq pairQ yes₁ yes₂)
            · right
              intro h
              cases h with
              | sigmaEta _ _ _ _ _ d₃ => exact no₂ d₃
              | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
          · right
            intro h
            cases h with
            | sigmaEta _ _ _ _ d₃ _ => exact no₁ d₃
            | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
      | spine sA _ _ _ _ _ => exact absurd sA SpineType.not_sigma
  | refl tx _ _ ih =>
      intro formed u u' second
      cases second with
      | refl ty _ d₂ =>
          rcases ih formed d₂ with yes | no
          · exact .inl (.refl tx ty yes)
          · right
            intro h
            cases h with
            | refl _ _ d₃ => exact no d₃
            | spine _ fT _ _ _ _ => exact absurd fT SpineForm.not_refl
      | spine _ fU _ _ _ _ =>
          right
          intro h
          cases h with
          | refl => exact absurd fU SpineForm.not_refl
          | spine _ fT _ _ _ _ => exact absurd fT SpineForm.not_refl
  | @spine n Γ t t' A U sA fT _ tt _ d ih =>
      intro formed u u' second
      cases second with
      | univ hu _ _ _ => exact absurd hu sA.not_universe
      | eta => exact absurd sA SpineType.not_pi
      | sigmaEta => exact absurd sA SpineType.not_sigma
      | refl =>
          right
          intro h
          cases h with
          | refl => exact absurd fT SpineForm.not_refl
          | spine _ _ fU _ _ _ => exact absurd fU SpineForm.not_refl
      | spine _ fU _ tu _ d₂ =>
          rcases ih formed d₂ with yes | no
          · exact .inl (.spine sA fT fU tt tu yes)
          · right
            intro h
            cases h with
            | univ hu _ _ _ => exact absurd hu sA.not_universe
            | eta => exact absurd sA SpineType.not_pi
            | sigmaEta => exact absurd sA SpineType.not_sigma
            | refl => exact absurd fT SpineForm.not_refl
            | spine _ _ _ _ _ d₃ =>
                obtain rfl := Algorithmic.spinesW_determined (Algorithmic.spines_determined t) d₃ d
                exact no d₃
  | var i =>
      intro formed u u' U' second
      cases second with
      | var j =>
          rcases Decidable.em (i = j) with same | different
          · subst same
            exact .inl ⟨_, .var i⟩
          · right
            rintro ⟨X, h⟩
            cases h
            exact different rfl
      | const =>
          right
          rintro ⟨X, h⟩
          cases h
      | app =>
          right
          rintro ⟨X, h⟩
          cases h
      | fst =>
          right
          rintro ⟨X, h⟩
          cases h
      | snd =>
          right
          rintro ⟨X, h⟩
          cases h
  | @const n Γ c type declared typed =>
      intro formed u u' U' second
      cases second with
      | @const _ _ c' _ _ _ =>
          rcases Decidable.em (c = c') with same | different
          · subst same
            exact .inl ⟨_, .const declared typed⟩
          · right
            rintro ⟨X, h⟩
            cases h
            exact different rfl
      | var =>
          right
          rintro ⟨X, h⟩
          cases h
      | app =>
          right
          rintro ⟨X, h⟩
          cases h
      | fst =>
          right
          rintro ⟨X, h⟩
          cases h
      | snd =>
          right
          rintro ⟨X, h⟩
          cases h
  | @app n Γ f f' a a' A B df _ ihf iha =>
      intro formed u u' U' second
      cases second with
      | app dg db =>
          rcases ihf formed dg with yesf | nof
          · have eA := Algorithmic.pi_domains facts roots heads algebra formed yesf dg
            rcases iha formed (conv db (CtxEq.refl _ formed) formed eA) with yesa | noa
            · exact .inl ⟨_, .app yesf yesa⟩
            · right
              rintro ⟨X, h⟩
              cases h with
              | app dg₃ da₃ =>
                  cases Algorithmic.spinesW_determined (Algorithmic.spines_determined f) dg₃ df
                  exact noa da₃
          · right
            rintro ⟨X, h⟩
            cases h with
            | app dg₃ _ =>
                cases Algorithmic.spinesW_determined (Algorithmic.spines_determined f) dg₃ df
                exact nof dg₃
      | var =>
          right
          rintro ⟨X, h⟩
          cases h
      | const =>
          right
          rintro ⟨X, h⟩
          cases h
      | fst =>
          right
          rintro ⟨X, h⟩
          cases h
      | snd =>
          right
          rintro ⟨X, h⟩
          cases h
  | @fst n Γ p p' A B dp ih =>
      intro formed u u' U' second
      cases second with
      | fst dq =>
          rcases ih formed dq with yes | no
          · exact .inl ⟨_, .fst yes⟩
          · right
            rintro ⟨X, h⟩
            cases h with
            | fst dq₃ =>
                cases Algorithmic.spinesW_determined (Algorithmic.spines_determined p) dq₃ dp
                exact no dq₃
      | var =>
          right
          rintro ⟨X, h⟩
          cases h
      | const =>
          right
          rintro ⟨X, h⟩
          cases h
      | app =>
          right
          rintro ⟨X, h⟩
          cases h
      | snd =>
          right
          rintro ⟨X, h⟩
          cases h
  | @snd n Γ p p' A B dp ih =>
      intro formed u u' U' second
      cases second with
      | snd dq =>
          rcases ih formed dq with yes | no
          · exact .inl ⟨_, .snd yes⟩
          · right
            rintro ⟨X, h⟩
            cases h with
            | snd dq₃ =>
                cases Algorithmic.spinesW_determined (Algorithmic.spines_determined p) dq₃ dp
                exact no dq₃
      | var =>
          right
          rintro ⟨X, h⟩
          cases h
      | const =>
          right
          rintro ⟨X, h⟩
          cases h
      | app =>
          right
          rintro ⟨X, h⟩
          cases h
      | fst =>
          right
          rintro ⟨X, h⟩
          cases h
  | @spinesW n Γ t t' U U₁ d rU fU ih =>
      intro formed u u' U' second
      cases second with
      | spinesW d₂ _ _ =>
          rcases ih formed d₂ with ⟨X, yes⟩ | no
          · obtain rfl := Algorithmic.spines_determined t yes d
            exact .inl (.spinesW yes rU fU)
          · right
            intro h
            cases h with
            | spinesW d₃ _ _ => exact no ⟨_, d₃⟩

variable (complete : AlgorithmicComplete S.R S.roles)
include complete

/-- The algorithmic comparison of two terms of a type in a formed context is
decided. -/
theorem Algorithmic.decide_terms {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (typedT : Typed S.R Γ t A) (typedU : Typed S.R Γ u A) :
    Algorithmic S.R S.roles (.terms Γ t u A) ∨ ¬ Algorithmic S.R S.roles (.terms Γ t u A) :=
  Algorithmic.decides facts roots heads algebra decideHeads
    (complete formed (.refl typedT)) formed
    (complete formed (.refl typedU))

/-- The algorithmic comparison of two types of a formed context is decided. -/
theorem Algorithmic.decide_types {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (typeA : IsType S.R Γ A) (typeB : IsType S.R Γ B) :
    Algorithmic S.R S.roles (.types Γ A B) ∨ ¬ Algorithmic S.R S.roles (.types Γ A B) :=
  Algorithmic.decides facts roots heads algebra decideHeads
    (complete.types typeA.refl formed) formed
    (complete.types typeB.refl formed)

/-- The typed equality between two terms of a type in a formed context is
decided. -/
theorem Equal.decide {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (typedT : Typed S.R Γ t A) (typedU : Typed S.R Γ u A) :
    Equal S.R Γ t u A ∨ ¬ Equal S.R Γ t u A := by
  rcases Algorithmic.decide_terms facts roots heads algebra decideHeads complete
      formed typedT typedU with yes | no
  · exact .inl (Algorithmic.sound facts roots heads algebra yes formed)
  · exact .inr fun equal =>
      no (complete formed equal)

/-- The equality of two types of a formed context is decided. -/
theorem TypeEq.decide {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (typeA : IsType S.R Γ A) (typeB : IsType S.R Γ B) :
    TypeEq S.R Γ A B ∨ ¬ TypeEq S.R Γ A B := by
  rcases Algorithmic.decide_types facts roots heads algebra decideHeads complete
      formed typeA typeB with yes | no
  · exact .inl (Algorithmic.sound facts roots heads algebra yes formed)
  · exact .inr fun equal =>
      no (complete.types equal formed)

end Decidability

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
