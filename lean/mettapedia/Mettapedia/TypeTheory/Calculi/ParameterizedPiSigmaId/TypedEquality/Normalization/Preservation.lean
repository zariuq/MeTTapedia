import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Injectivity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Generation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Algorithm

/-!
# Preservation

Typing is preserved by weak-head reduction and by every contextual step of the
rule package, and a step between typed terms is a typed equality at their
type. Two properties of the rule package are needed and taken as
hypotheses, because they are admission obligations rather than consequences:
its declared root computations preserve typing, and its head equality steps
preserve typing.

What a derivable statement presupposes holds syntactically, for every rule
package whose universes have a level model (`Derivable.presupposed`): the type
of a typed term is a type, and both sides of a typed equality are typed at its
type.

The contractions need inversion of typings of λ-abstractions and pairs, which
uses injectivity of dependent function and pair types and their
discrimination from heads; these come from the facts about the weak-head forms
of types (`FormFacts`), whichever model supplies them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Context conversion -/

section ContextConversion

variable {R : Rules Head}

theorem SubstMor.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    (equal : TypeEq R Γ A' A) : SubstMor R (.snoc Γ A) (.snoc Γ A') ids := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · show Typed R (.snoc Γ A') (.var 0) (Presentation.subst ids (Presentation.rename wk A))
    rw [subst_ids]
    exact Typed.convType (.var 0) (equal.rename (CtxRen.wk Γ A'))
  · show Typed R (.snoc Γ A') (.var j.succ)
      (Presentation.subst ids (Presentation.rename wk (Ctx.lookup Γ j)))
    rw [subst_ids]
    exact .var j.succ

/-- Changing the last context entry to an equal type. -/
theorem Typed.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {t T : Tm Head (n + 1)}
    (typing : Typed R (.snoc Γ A) t T) (equal : TypeEq R Γ A A') :
    Typed R (.snoc Γ A') t T := by
  simpa using typing.substitute (SubstMor.ctxConv equal.symm)

/-- Changing the last context entry to an equal type. -/
theorem Equal.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {a b T : Tm Head (n + 1)}
    (equality : Equal R (.snoc Γ A) a b T) (equal : TypeEq R Γ A A') :
    Equal R (.snoc Γ A') a b T := by
  simpa using equality.substitute (SubstMor.ctxConv equal.symm)

/-- A context whose last entry is usable at another maps into it by the
identity. -/
theorem SubstMor.ctxBelow {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    (le : Below R Γ A' A) : SubstMor R (.snoc Γ A) (.snoc Γ A') ids := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · show Typed R (.snoc Γ A') (.var 0) (Presentation.subst ids (Presentation.rename wk A))
    rw [subst_ids]
    exact .sub (.var 0) (Derivable.renames le (CtxRen.wk Γ A'))
  · show Typed R (.snoc Γ A') (.var j.succ)
      (Presentation.subst ids (Presentation.rename wk (Ctx.lookup Γ j)))
    rw [subst_ids]
    exact .var j.succ

/-- Changing the last context entry to a type usable at it. -/
theorem Typed.ctxBelow {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {t T : Tm Head (n + 1)}
    (typing : Typed R (.snoc Γ A) t T) (le : Below R Γ A' A) : Typed R (.snoc Γ A') t T := by
  simpa using typing.substitute (SubstMor.ctxBelow le)

/-- Changing the last context entry of a subtyping statement to an equal type. -/
theorem Below.ctxConv {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B C : Tm Head (n + 1)}
    (le : Below R (.snoc Γ A) B C) (equal : TypeEq R Γ A A') : Below R (.snoc Γ A') B C := by
  simpa using Derivable.substitutes le (SubstMor.ctxConv equal.symm)

/-- Changing the last context entry of a subtyping statement to a type usable
at it. -/
theorem Below.ctxBelow {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B C : Tm Head (n + 1)}
    (le : Below R (.snoc Γ A) B C) (below : Below R Γ A' A) : Below R (.snoc Γ A') B C := by
  simpa using Derivable.substitutes le (SubstMor.ctxBelow below)

/-- Types equal at a universe are usable at each other. -/
theorem TypeEq.below {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq R Γ A B) :
    Below R Γ A B := by
  obtain ⟨u, hu, e⟩ := equal
  exact .subEqual e hu

/-- A type is usable at itself. -/
theorem IsType.below_refl {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (type : IsType R Γ A) :
    Below R Γ A A :=
  type.refl.below

/-- A chain of conversions, universe raises and subtyping steps that ends in a
type is one subtyping statement. -/
theorem TypeLe.toBelow {n : Nat} {Γ : Ctx Head n} {X Y : Tm Head n} (le : TypeLe R Γ X Y)
    (typeY : IsType R Γ Y) : Below R Γ X Y := by
  induction le with
  | refl => exact typeY.below_refl
  | conv e hu _ ih => exact .subTrans (.subEqual e hu) (ih typeY)
  | cumul c _ ih => exact .subTrans (.subUniv c) (ih typeY)
  | sub le _ ih => exact .subTrans le (ih typeY)

/-- Instantiating equal families at one argument. -/
theorem TypeEq.instantiate {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n}
    {B B' : Tm Head (n + 1)} (equal : TypeEq R (.snoc Γ A) B B') (typing : Typed R Γ a A) :
    TypeEq R Γ (inst0 a B) (inst0 a B') := by
  obtain ⟨v, hv, e⟩ := equal
  exact ⟨v, hv, e.substitute (SubstMor.single typing)⟩

/-- Instantiating one family at equal arguments. -/
theorem TypeEq.of_instantiateEq {n : Nat} {Γ : Ctx Head n} {A a a' : Tm Head n}
    {B : Tm Head (n + 1)} {v : Head} (family : Typed R (.snoc Γ A) B (.head v))
    (hv : R.isUniverse v) (typing : Typed R Γ a A) (equal : Equal R Γ a a' A) :
    TypeEq R Γ (inst0 a B) (inst0 a' B) :=
  ⟨v, hv, family.instantiateEq typing equal⟩

end ContextConversion

/-! ## Obligations of the rule package -/

/-- Declared root computations preserve typing in formed contexts. -/
def RootPreserving (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {l r A : Tm Head n}, CtxFormed R Γ → R.computation.step l r →
    Typed R Γ l A → Typed R Γ r A

/-- Head equality steps preserve typing. -/
def HeadPreserving (R : Rules Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {h h' : Head} {A : Tm Head n}, R.headEq h h' →
    Typed R Γ (.head h) A → Typed R Γ (.head h') A

/-! ## Presuppositions -/

section Presuppositions

variable {R : Rules Head}

/-- The parts of a dependent function or pair type that is a type. -/
theorem IsType.pi_parts {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (formed' : IsType R Γ (.pi A B)) :
    (∃ u, R.isUniverse u ∧ Typed R Γ A (.head u)) ∧
      ∃ v, R.isUniverse v ∧ Typed R (.snoc Γ A) B (.head v) := by
  obtain ⟨w, _, typing⟩ := formed'
  obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := typing.generation
  exact ⟨⟨u, hu, tA⟩, v, hv, tB⟩

theorem IsType.sigma_parts {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
    (formed' : IsType R Γ (.sigma A B)) :
    (∃ u, R.isUniverse u ∧ Typed R Γ A (.head u)) ∧
      ∃ v, R.isUniverse v ∧ Typed R (.snoc Γ A) B (.head v) := by
  obtain ⟨w, _, typing⟩ := formed'
  obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := typing.generation
  exact ⟨⟨u, hu, tA⟩, v, hv, tB⟩

/-- What a statement presupposes in a formed context: the type of a typing is a
type; both sides of an equality are typed at its type, which is a type; both
sides of a subtyping statement are types. -/
abbrev Presupposed (R : Rules Head) : Statement Head → Prop
  | .typing Γ _ A => CtxFormed R Γ → IsType R Γ A
  | .equality Γ a b A => CtxFormed R Γ → Typed R Γ a A ∧ Typed R Γ b A ∧ IsType R Γ A
  | .sub Γ A B => CtxFormed R Γ → IsType R Γ A ∧ IsType R Γ B

/-- **Syntactic validity**: in a formed context, what a derivable statement
presupposes holds, for every rule package whose universes have a level model.
The proof is one induction over derivations: a computation rule and a head
equality carry the typings of both of their sides, a congruence rule gives its
right side's typing through context conversion and functionality, and the
formers' types are universes. -/
theorem Derivable.presupposed (levels : LevelModel R L) {statement : Statement Head}
    (derivation : Derivable R statement) : Presupposed R statement := by
  have universeType : ∀ {n : Nat} {Γ : Ctx Head n} {u : Head}, R.isUniverse u →
      IsType R Γ (.head u) := fun hu => by
    obtain ⟨v, hv, typing, _⟩ := levels.successor hu
    exact ⟨v, hv, .headType typing⟩
  induction derivation with
  | headType head => exact fun _ => universeType (levels.ground_typing head)
  | var i => exact fun formed => formed.lookup i
  | const _ typedType hu _ =>
      exact fun _ => ⟨_, hu, Typed.rename (ρ := Fin.elim0) typedType (fun i => Fin.elim0 i)⟩
  | piForm _ _ _ _ join => exact fun _ => universeType (levels.join_level join).1
  | sigmaForm _ _ _ _ join => exact fun _ => universeType (levels.join_level join).1
  | lamIntro tPi hu _ _ _ => exact fun _ => ⟨_, hu, tPi⟩
  | appElim _ ta ihF _ =>
      intro formed
      obtain ⟨_, v, hv, tB⟩ := IsType.pi_parts (ihF formed)
      exact ⟨v, hv, Typed.instantiate tB ta⟩
  | pairIntro tS hu _ _ _ _ _ => exact fun _ => ⟨_, hu, tS⟩
  | fstElim _ ihP =>
      intro formed
      exact (IsType.sigma_parts (ihP formed)).1
  | sndElim tp ihP =>
      intro formed
      obtain ⟨_, v, hv, tB⟩ := IsType.sigma_parts (ihP formed)
      exact ⟨v, hv, Typed.instantiate tB (.fstElim tp)⟩
  | idForm _ hu _ _ _ _ _ => exact fun _ => universeType hu
  | reflIntro ta ihA =>
      intro formed
      obtain ⟨u, hu, tA⟩ := ihA formed
      exact ⟨u, hu, .idForm tA hu ta ta⟩
  | sub _ _ _ ihLe => exact fun formed => (ihLe formed).2
  | conv _ _ hu _ ihE => exact fun formed => ⟨_, hu, (ihE formed).2.1⟩
  | refl ta ihA => exact fun formed => ⟨ta, ta, ihA formed⟩
  | symm _ ih =>
      intro formed
      obtain ⟨ta, tb, tA⟩ := ih formed
      exact ⟨tb, ta, tA⟩
  | trans _ _ ih₁ ih₂ => exact fun formed => ⟨(ih₁ formed).1, (ih₂ formed).2.1, (ih₁ formed).2.2⟩
  | convEq _ e hu ih ihE =>
      intro formed
      obtain ⟨ta, tb, _⟩ := ih formed
      exact ⟨.conv ta e hu, .conv tb e hu, ⟨_, hu, (ihE formed).2.1⟩⟩
  | subEq _ le ih ihLe =>
      intro formed
      obtain ⟨ta, tb, _⟩ := ih formed
      exact ⟨.sub ta le, .sub tb le, (ihLe formed).2⟩
  | headEq _ typing typing' ih _ => exact fun formed => ⟨typing, typing', ih formed⟩
  | piCong eA hu _ hv join ihA ihB =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨tB, tB', _⟩ := ihB (.snoc formed ⟨_, hu, tA⟩)
      exact ⟨.piForm tA hu tB hv join, .piForm tA' hu (Typed.ctxConv tB' ⟨_, hu, eA⟩) hv join,
        universeType (levels.join_level join).1⟩
  | sigmaCong eA hu _ hv join ihA ihB =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨tB, tB', _⟩ := ihB (.snoc formed ⟨_, hu, tA⟩)
      exact ⟨.sigmaForm tA hu tB hv join,
        .sigmaForm tA' hu (Typed.ctxConv tB' ⟨_, hu, eA⟩) hv join,
        universeType (levels.join_level join).1⟩
  | idCong eA hu _ _ ihA iha ihb =>
      intro formed
      obtain ⟨tA, tA', _⟩ := ihA formed
      obtain ⟨ta, ta', _⟩ := iha formed
      obtain ⟨tb, tb', _⟩ := ihb formed
      exact ⟨.idForm tA hu ta tb, .idForm tA' hu (.conv ta' eA hu) (.conv tb' eA hu),
        universeType hu⟩
  | lamCong tPi hu _ _ ihBody =>
      intro formed
      obtain ⟨⟨u', hu', tA⟩, _⟩ := IsType.pi_parts ⟨_, hu, tPi⟩
      obtain ⟨tb, tb', _⟩ := ihBody (.snoc formed ⟨u', hu', tA⟩)
      exact ⟨.lamIntro tPi hu tb, .lamIntro tPi hu tb', ⟨_, hu, tPi⟩⟩
  | appCong _ ea ihF ihA =>
      intro formed
      obtain ⟨tf, tg, typePi⟩ := ihF formed
      obtain ⟨ta, tb, _⟩ := ihA formed
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts typePi
      exact ⟨.appElim tf ta,
        Typed.convType (.appElim tg tb) (TypeEq.of_instantiateEq family hv ta ea).symm,
        ⟨v, hv, Typed.instantiate family ta⟩⟩
  | pairCong tS hu ea _ _ iha ihb =>
      intro formed
      obtain ⟨ta, ta', _⟩ := iha formed
      obtain ⟨tb, tb', _⟩ := ihb formed
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨_, hu, tS⟩
      exact ⟨.pairIntro tS hu ta tb,
        .pairIntro tS hu ta' (Typed.convType tb' (TypeEq.of_instantiateEq family hv ta ea)),
        ⟨_, hu, tS⟩⟩
  | fstCong _ ih =>
      intro formed
      obtain ⟨tp, tq, typeSigma⟩ := ih formed
      exact ⟨.fstElim tp, .fstElim tq, (IsType.sigma_parts typeSigma).1⟩
  | sndCong e ih =>
      intro formed
      obtain ⟨tp, tq, typeSigma⟩ := ih formed
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts typeSigma
      exact ⟨.sndElim tp, Typed.convType (.sndElim tq)
          (TypeEq.of_instantiateEq family hv (.fstElim tp) (.fstCong e)).symm,
        ⟨v, hv, Typed.instantiate family (.fstElim tp)⟩⟩
  | reflCong e ih =>
      intro formed
      obtain ⟨ta, tb, u, hu, tA⟩ := ih formed
      exact ⟨.reflIntro ta,
        .conv (.reflIntro tb) (.idCong (.refl tA) hu (.symm e) (.symm e)) hu,
        ⟨u, hu, .idForm tA hu ta ta⟩⟩
  | betaPi tPi hu tb ta _ _ _ =>
      intro _
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨_, hu, tPi⟩
      exact ⟨.appElim (.lamIntro tPi hu tb) ta, Typed.instantiate tb ta,
        ⟨v, hv, Typed.instantiate family ta⟩⟩
  | betaFst tS hu ta tb _ _ _ =>
      intro _
      exact ⟨.fstElim (.pairIntro tS hu ta tb), ta, (IsType.sigma_parts ⟨_, hu, tS⟩).1⟩
  | betaSnd tS hu ta tb _ _ _ =>
      intro _
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨_, hu, tS⟩
      exact ⟨Typed.convType (.sndElim (.pairIntro tS hu ta tb))
          (TypeEq.of_instantiateEq family hv (.fstElim (.pairIntro tS hu ta tb))
            (.betaFst tS hu ta tb)),
        tb, ⟨v, hv, Typed.instantiate family ta⟩⟩
  | root _ tl tr ihL _ => exact fun formed => ⟨tl, tr, ihL formed⟩
  | etaPi tf tg _ ihF _ _ => exact fun formed => ⟨tf, tg, ihF formed⟩
  | etaSigma tp tq _ _ ihP _ _ _ => exact fun formed => ⟨tp, tq, ihP formed⟩
  | subEqual _ hu ih =>
      intro formed
      obtain ⟨tA, tB, _⟩ := ih formed
      exact ⟨⟨_, hu, tA⟩, ⟨_, hu, tB⟩⟩
  | subUniv c =>
      obtain ⟨hu, hv, _⟩ := levels.cumulative_universe c
      exact fun _ => ⟨universeType hu, universeType hv⟩
  | subPi tPi hu tPi' hu' _ _ _ _ _ _ _ => exact fun _ => ⟨⟨_, hu, tPi⟩, ⟨_, hu', tPi'⟩⟩
  | subSigma tS hu tS' hu' _ _ _ _ _ _ => exact fun _ => ⟨⟨_, hu, tS⟩, ⟨_, hu', tS'⟩⟩
  | subTrans _ _ ih₁ ih₂ => exact fun formed => ⟨(ih₁ formed).1, (ih₂ formed).2⟩

end Presuppositions

variable {S : Setting Head L}

section Presupposed

/-- The type of a typed term is a type. -/
theorem Typed.isType {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (typing : Typed S.R Γ t T) (formed : CtxFormed S.R Γ) : IsType S.R Γ T :=
  Derivable.presupposed S.levels typing formed

/-- Both sides of a typed equality are typed. -/
theorem Equal.typed {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : Equal S.R Γ a b A) (formed : CtxFormed S.R Γ) :
    Typed S.R Γ a A ∧ Typed S.R Γ b A :=
  let ⟨ta, tb, _⟩ := Derivable.presupposed S.levels equal formed
  ⟨ta, tb⟩

/-- A universe head is a type. -/
theorem IsType.head_of_universe {n : Nat} {Γ : Ctx Head n} {u : Head} (hu : S.R.isUniverse u) :
    IsType S.R Γ (.head u) := by
  obtain ⟨v, hv, typing, _⟩ := S.levels.successor hu
  exact ⟨v, hv, .headType typing⟩

/-- Levels of heads that are the same head agree. -/
theorem HeadSame.level_eq {h h' : Head} (same : HeadSame S.R h h') :
    S.levels.level h = S.levels.level h' := by
  rcases same with rfl | equal
  · rfl
  · exact (S.levels.headEq_level equal).2

/-- Both sides of an equality of types are types. -/
theorem TypeEq.isType {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq S.R Γ A B)
    (formed : CtxFormed S.R Γ) : IsType S.R Γ A ∧ IsType S.R Γ B := by
  obtain ⟨u, hu, e⟩ := equal
  obtain ⟨tA, tB⟩ := Equal.typed e formed
  exact ⟨⟨u, hu, tA⟩, ⟨u, hu, tB⟩⟩

/-- Both sides of a subtyping statement are types. -/
theorem Below.isTypes {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (le : Below S.R Γ A B)
    (formed : CtxFormed S.R Γ) : IsType S.R Γ A ∧ IsType S.R Γ B :=
  Derivable.presupposed S.levels le formed

end Presupposed

/-! ## Inversion, from the facts about weak-head forms -/

section Inversion

variable (facts : FormFacts S.R S.roles)
include facts

/-- A type usable at a dependent function type is one, with an equal domain
and a codomain usable at the other's. -/
theorem Below.pi_inv {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : Below S.R Γ X T)
    (formed : CtxFormed S.R Γ) {A' : Tm Head n} {B' : Tm Head (n + 1)}
    (eT : TypeEq S.R Γ T (.pi A' B')) :
    ∃ A B, TypeEq S.R Γ X (.pi A B) ∧ TypeEq S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B' := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ →
      ∀ {A' : Tm Head n} {B' : Tm Head (n + 1)}, TypeEq S.R Γ T (.pi A' B') →
        ∃ A B, TypeEq S.R Γ X (.pi A B) ∧ TypeEq S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eT
  case equal =>
    intro n Γ X T u e hu formed A' B' eT
    have eX : TypeEq S.R Γ X (.pi A' B') := TypeEq.trans S.levels ⟨u, hu, e⟩ eT
    obtain ⟨typeA, typeB⟩ := IsType.pi_parts (TypeEq.isType eT formed).2
    exact ⟨A', B', eX, IsType.refl typeA, IsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A' B' eT
    exact absurd eT.symm (TypeEq.pi_ne_head facts formed)
  case pi =>
    intro n Γ A A₁ B B₁ u u₁ w tPi hu _ _ eA hw leB _ formed A' B' eT
    obtain ⟨eA', eB'⟩ := TypeEq.pi_injective facts eT formed
    have eAA₁ : TypeEq S.R Γ A A₁ := ⟨w, hw, eA⟩
    exact ⟨A, B, IsType.refl ⟨u, hu, tPi⟩, TypeEq.trans S.levels eAA₁ eA',
      .subTrans leB (Below.ctxConv eB'.below eAA₁.symm)⟩
  case sigma =>
    intro n Γ A A₁ B B₁ u u₁ _ _ _ _ _ _ _ _ formed A' B' eT
    exact absurd eT.symm (TypeEq.pi_ne_sigma facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A' B' eT
    obtain ⟨A₁, B₁, eY, eA₁, leB₁⟩ := ih₂ formed eT
    obtain ⟨A₀, B₀, eX, eA₀, leB₀⟩ := ih₁ formed eY
    exact ⟨A₀, B₀, eX, TypeEq.trans S.levels eA₀ eA₁, .subTrans leB₀ (Below.ctxConv leB₁ eA₀.symm)⟩

/-- A type usable at a dependent pair type is one, with a domain and a codomain
usable at the other's. -/
theorem Below.sigma_inv {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : Below S.R Γ X T)
    (formed : CtxFormed S.R Γ) {A' : Tm Head n} {B' : Tm Head (n + 1)}
    (eT : TypeEq S.R Γ T (.sigma A' B')) :
    ∃ A B, TypeEq S.R Γ X (.sigma A B) ∧ Below S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B' := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ →
      ∀ {A' : Tm Head n} {B' : Tm Head (n + 1)}, TypeEq S.R Γ T (.sigma A' B') →
        ∃ A B, TypeEq S.R Γ X (.sigma A B) ∧ Below S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eT
  case equal =>
    intro n Γ X T u e hu formed A' B' eT
    have eX : TypeEq S.R Γ X (.sigma A' B') := TypeEq.trans S.levels ⟨u, hu, e⟩ eT
    obtain ⟨typeA, typeB⟩ := IsType.sigma_parts (TypeEq.isType eT formed).2
    exact ⟨A', B', eX, IsType.below_refl typeA, IsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A' B' eT
    exact absurd eT.symm (TypeEq.sigma_ne_head facts formed)
  case pi =>
    intro n Γ A A₁ B B₁ u u₁ w _ _ _ _ _ _ _ _ formed A' B' eT
    exact absurd eT (TypeEq.pi_ne_sigma facts formed)
  case sigma =>
    intro n Γ A A₁ B B₁ u u₁ tS hu _ _ leA leB _ _ formed A' B' eT
    obtain ⟨eA', eB'⟩ := TypeEq.sigma_injective facts eT formed
    exact ⟨A, B, IsType.refl ⟨u, hu, tS⟩, .subTrans leA eA'.below,
      .subTrans leB (Below.ctxBelow eB'.below leA)⟩
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A' B' eT
    obtain ⟨A₁, B₁, eY, leA₁, leB₁⟩ := ih₂ formed eT
    obtain ⟨A₀, B₀, eX, leA₀, leB₀⟩ := ih₁ formed eY
    exact ⟨A₀, B₀, eX, .subTrans leA₀ leA₁, .subTrans leB₀ (Below.ctxBelow leB₁ leA₀)⟩

/-- A dependent function type is usable only at dependent function types with
an equal domain and a codomain its codomain is usable at. -/
theorem Below.pi_source {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : Below S.R Γ X T)
    (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)}
    (eX : TypeEq S.R Γ X (.pi A B)) :
    ∃ A' B', TypeEq S.R Γ T (.pi A' B') ∧ TypeEq S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B' := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ →
      ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, TypeEq S.R Γ X (.pi A B) →
        ∃ A' B', TypeEq S.R Γ T (.pi A' B') ∧ TypeEq S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro n Γ X T u e hu formed A B eX
    have eT : TypeEq S.R Γ T (.pi A B) := TypeEq.trans S.levels (TypeEq.symm ⟨u, hu, e⟩) eX
    obtain ⟨typeA, typeB⟩ := IsType.pi_parts (TypeEq.isType eX formed).2
    exact ⟨A, B, eT, IsType.refl typeA, IsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A B eX
    exact absurd eX.symm (TypeEq.pi_ne_head facts formed)
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ w _ _ tPi₁ hu₁ eA hw leB _ formed A B eX
    obtain ⟨eA₀, eB₀⟩ := TypeEq.pi_injective facts eX formed
    have eA₀₁ : TypeEq S.R Γ A₀ A₁ := ⟨w, hw, eA⟩
    exact ⟨A₁, B₁, IsType.refl ⟨u₁, hu₁, tPi₁⟩, TypeEq.trans S.levels eA₀.symm eA₀₁,
      Below.ctxConv (Derivable.subTrans eB₀.symm.below leB) eA₀⟩
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ _ _ _ _ _ _ _ _ formed A B eX
    exact absurd eX (TypeEq.pi_ne_sigma facts formed ∘ TypeEq.symm)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A B eX
    obtain ⟨A₁, B₁, eY, eA₁, leB₁⟩ := ih₁ formed eX
    obtain ⟨A₂, B₂, eT, eA₂, leB₂⟩ := ih₂ formed eY
    exact ⟨A₂, B₂, eT, TypeEq.trans S.levels eA₁ eA₂, .subTrans leB₁ (Below.ctxConv leB₂ eA₁.symm)⟩

/-- A dependent pair type is usable only at dependent pair types with a domain
and a codomain its own are usable at. -/
theorem Below.sigma_source {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : Below S.R Γ X T)
    (formed : CtxFormed S.R Γ) {A : Tm Head n} {B : Tm Head (n + 1)}
    (eX : TypeEq S.R Γ X (.sigma A B)) :
    ∃ A' B', TypeEq S.R Γ T (.sigma A' B') ∧ Below S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B' := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ →
      ∀ {A : Tm Head n} {B : Tm Head (n + 1)}, TypeEq S.R Γ X (.sigma A B) →
        ∃ A' B', TypeEq S.R Γ T (.sigma A' B') ∧ Below S.R Γ A A' ∧ Below S.R (.snoc Γ A) B B')
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro n Γ X T u e hu formed A B eX
    have eT : TypeEq S.R Γ T (.sigma A B) := TypeEq.trans S.levels (TypeEq.symm ⟨u, hu, e⟩) eX
    obtain ⟨typeA, typeB⟩ := IsType.sigma_parts (TypeEq.isType eX formed).2
    exact ⟨A, B, eT, IsType.below_refl typeA, IsType.below_refl typeB⟩
  case univ =>
    intro n Γ u v _ formed A B eX
    exact absurd eX.symm (TypeEq.sigma_ne_head facts formed)
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ w _ _ _ _ _ _ _ _ formed A B eX
    exact absurd eX (TypeEq.pi_ne_sigma facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ u u₁ _ _ tS₁ hu₁ leA leB _ _ formed A B eX
    obtain ⟨eA₀, eB₀⟩ := TypeEq.sigma_injective facts eX formed
    exact ⟨A₁, B₁, IsType.refl ⟨u₁, hu₁, tS₁⟩, .subTrans eA₀.symm.below leA,
      Below.ctxConv (Derivable.subTrans eB₀.symm.below leB) eA₀⟩
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed A B eX
    obtain ⟨A₁, B₁, eY, leA₁, leB₁⟩ := ih₁ formed eX
    obtain ⟨A₂, B₂, eT, leA₂, leB₂⟩ := ih₂ formed eY
    exact ⟨A₂, B₂, eT, .subTrans leA₁ leA₂, .subTrans leB₁ (Below.ctxBelow leB₂ leA₁)⟩

/-- A universe is usable only at universes of a level at least its own. -/
theorem Below.universe_source {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n}
    (le : Below S.R Γ X T) (formed : CtxFormed S.R Γ) {u : Head} (hu : S.R.isUniverse u)
    (eX : TypeEq S.R Γ X (.head u)) :
    ∃ v, S.R.isUniverse v ∧ TypeEq S.R Γ T (.head v) ∧ S.levels.level u ≤ S.levels.level v := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ → ∀ {u : Head},
      S.R.isUniverse u → TypeEq S.R Γ X (.head u) →
        ∃ v, S.R.isUniverse v ∧ TypeEq S.R Γ T (.head v) ∧ S.levels.level u ≤ S.levels.level v)
    ?equal ?univ ?pi ?sigma ?trans le formed hu eX
  case equal =>
    intro n Γ X T w e hw formed u hu eX
    exact ⟨u, hu, TypeEq.trans S.levels (TypeEq.symm ⟨w, hw, e⟩) eX, le_refl _⟩
  case univ =>
    intro n Γ u₀ v₀ c formed u hu eX
    obtain ⟨_, hv₀, le⟩ := S.levels.cumulative_universe c
    have same := HeadSame.level_eq (TypeEq.head_injective facts eX formed)
    exact ⟨v₀, hv₀, IsType.refl (IsType.head_of_universe hv₀), same ▸ le⟩
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ formed u hu eX
    exact absurd eX (TypeEq.pi_ne_head facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ formed u hu eX
    exact absurd eX (TypeEq.sigma_ne_head facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed u hu eX
    obtain ⟨w, hw, eY, le₁⟩ := ih₁ formed hu eX
    obtain ⟨v, hv, eT, le₂⟩ := ih₂ formed hw eY
    exact ⟨v, hv, eT, le_trans le₁ le₂⟩

/-- A type usable at a universe is a universe of a level at most its own. -/
theorem Below.universe_target {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n}
    (le : Below S.R Γ X T) (formed : CtxFormed S.R Γ) {v : Head} (hv : S.R.isUniverse v)
    (eT : TypeEq S.R Γ T (.head v)) :
    ∃ u, S.R.isUniverse u ∧ TypeEq S.R Γ X (.head u) ∧ S.levels.level u ≤ S.levels.level v := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ → ∀ {v : Head},
      S.R.isUniverse v → TypeEq S.R Γ T (.head v) →
        ∃ u, S.R.isUniverse u ∧ TypeEq S.R Γ X (.head u) ∧ S.levels.level u ≤ S.levels.level v)
    ?equal ?univ ?pi ?sigma ?trans le formed hv eT
  case equal =>
    intro n Γ X T w e hw formed v hv eT
    exact ⟨v, hv, TypeEq.trans S.levels ⟨w, hw, e⟩ eT, le_refl _⟩
  case univ =>
    intro n Γ u₀ v₀ c formed v hv eT
    obtain ⟨hu₀, _, le⟩ := S.levels.cumulative_universe c
    have same := HeadSame.level_eq (TypeEq.head_injective facts eT formed)
    exact ⟨u₀, hu₀, IsType.refl (IsType.head_of_universe hu₀), same ▸ le⟩
  case pi =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ _ formed v hv eT
    exact absurd eT (TypeEq.pi_ne_head facts formed)
  case sigma =>
    intro n Γ A₀ A₁ B₀ B₁ _ _ _ _ _ _ _ _ _ _ formed v hv eT
    exact absurd eT (TypeEq.sigma_ne_head facts formed)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed v hv eT
    obtain ⟨w, hw, eY, le₂⟩ := ih₂ formed hv eT
    obtain ⟨u, hu, eX, le₁⟩ := ih₁ formed hw eY
    exact ⟨u, hu, eX, le_trans le₁ le₂⟩

omit facts in
/-- A type equal to no universe, dependent function or pair type is usable only
at types equal to it. -/
theorem Below.rigid {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : Below S.R Γ X T)
    (formed : CtxFormed S.R Γ)
    (notUniverse : ∀ u, S.R.isUniverse u → ¬ TypeEq S.R Γ X (.head u))
    (notPi : ∀ A B, ¬ TypeEq S.R Γ X (.pi A B)) (notSigma : ∀ A B, ¬ TypeEq S.R Γ X (.sigma A B)) :
    TypeEq S.R Γ X T := by
  refine Below.induction (motive := fun n Γ X T => CtxFormed S.R Γ →
      (∀ u, S.R.isUniverse u → ¬ TypeEq S.R Γ X (.head u)) →
      (∀ A B, ¬ TypeEq S.R Γ X (.pi A B)) → (∀ A B, ¬ TypeEq S.R Γ X (.sigma A B)) →
        TypeEq S.R Γ X T)
    ?equal ?univ ?pi ?sigma ?trans le formed notUniverse notPi notSigma
  case equal =>
    intro n Γ X T u e hu _ _ _ _
    exact ⟨u, hu, e⟩
  case univ =>
    intro n Γ u v c _ notUniverse _ _
    obtain ⟨hu, _, _⟩ := S.levels.cumulative_universe c
    exact absurd (IsType.refl (IsType.head_of_universe hu)) (notUniverse u hu)
  case pi =>
    intro n Γ A A₁ B B₁ u _ _ tPi hu _ _ _ _ _ _ _ _ notPi _
    exact absurd (IsType.refl ⟨u, hu, tPi⟩) (notPi A B)
  case sigma =>
    intro n Γ A A₁ B B₁ u _ tS hu _ _ _ _ _ _ _ _ _ notSigma
    exact absurd (IsType.refl ⟨u, hu, tS⟩) (notSigma A B)
  case trans =>
    intro n Γ X Y T _ _ ih₁ ih₂ formed notUniverse notPi notSigma
    have eXY := ih₁ formed notUniverse notPi notSigma
    have eYT := ih₂ formed
      (fun u hu e => notUniverse u hu (TypeEq.trans S.levels eXY e))
      (fun A B e => notPi A B (TypeEq.trans S.levels eXY e))
      (fun A B e => notSigma A B (TypeEq.trans S.levels eXY e))
    exact TypeEq.trans S.levels eXY eYT

/-- Inversion of a typed abstraction at a dependent function type. -/
theorem Typed.lam_inv {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {body B : Tm Head (n + 1)}
    (typing : Typed S.R Γ (.lam body) (.pi A B)) (formed : CtxFormed S.R Γ) :
    Typed S.R (.snoc Γ A) body B := by
  obtain ⟨A', B', u, tPi, hu, tb, le⟩ := typing.generation
  have below := TypeLe.toBelow le (Typed.isType typing formed)
  obtain ⟨A₀, B₀, eX, eA, leB⟩ :=
    Below.pi_inv facts below formed (IsType.refl (Typed.isType typing formed))
  obtain ⟨eA', eB'⟩ := TypeEq.pi_injective facts eX formed
  exact Typed.ctxConv (.sub (Typed.convType tb eB') (Below.ctxConv leB eA'.symm))
    (TypeEq.trans S.levels eA' eA)

/-- Inversion of a typed pair at a dependent pair type. -/
theorem Typed.pair_inv {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {B : Tm Head (n + 1)}
    (typing : Typed S.R Γ (.pair a b) (.sigma A B)) (formed : CtxFormed S.R Γ) :
    Typed S.R Γ a A ∧ Typed S.R Γ b (inst0 a B) := by
  obtain ⟨A', B', u, tSigma, hu, ta, tb, le⟩ := typing.generation
  have below := TypeLe.toBelow le (Typed.isType typing formed)
  obtain ⟨A₀, B₀, eX, leA, leB⟩ :=
    Below.sigma_inv facts below formed (IsType.refl (Typed.isType typing formed))
  obtain ⟨eA', eB'⟩ := TypeEq.sigma_injective facts eX formed
  have ta₀ : Typed S.R Γ a A₀ := Typed.convType ta eA'
  have leB' : Below S.R (.snoc Γ A') B' B := .subTrans eB'.below (Below.ctxConv leB eA'.symm)
  exact ⟨.sub ta₀ leA, .sub tb (Derivable.substitutes leB' (SubstMor.single ta))⟩

/-- A chain from a dependent function type to another relates their domains by
equality and their codomains by subtyping. -/
theorem TypeLe.pi_parts {n : Nat} {Γ : Ctx Head n} {A A₁ : Tm Head n} {B B₁ : Tm Head (n + 1)}
    (le : TypeLe S.R Γ (.pi A B) (.pi A₁ B₁)) (type₁ : IsType S.R Γ (.pi A₁ B₁))
    (formed : CtxFormed S.R Γ) : TypeEq S.R Γ A A₁ ∧ Below S.R (.snoc Γ A) B B₁ := by
  obtain ⟨A₀, B₀, eX, eA, leB⟩ :=
    Below.pi_inv facts (TypeLe.toBelow le type₁) formed (IsType.refl type₁)
  obtain ⟨eA', eB'⟩ := TypeEq.pi_injective facts eX formed
  exact ⟨TypeEq.trans S.levels eA' eA, .subTrans eB'.below (Below.ctxConv leB eA'.symm)⟩

/-- A chain from a dependent pair type to another relates their domains and
their codomains by subtyping. -/
theorem TypeLe.sigma_parts {n : Nat} {Γ : Ctx Head n} {A A₁ : Tm Head n}
    {B B₁ : Tm Head (n + 1)} (le : TypeLe S.R Γ (.sigma A B) (.sigma A₁ B₁))
    (type₁ : IsType S.R Γ (.sigma A₁ B₁)) (formed : CtxFormed S.R Γ) :
    Below S.R Γ A A₁ ∧ Below S.R (.snoc Γ A) B B₁ := by
  obtain ⟨A₀, B₀, eX, leA, leB⟩ :=
    Below.sigma_inv facts (TypeLe.toBelow le type₁) formed (IsType.refl type₁)
  obtain ⟨eA', eB'⟩ := TypeEq.sigma_injective facts eX formed
  exact ⟨.subTrans eA'.below leA, .subTrans eB'.below (Below.ctxConv leB eA'.symm)⟩

omit facts in
/-- A chain from a type equal to no universe, dependent function or pair type
ends in a type equal to it. -/
theorem TypeLe.rigid {n : Nat} {Γ : Ctx Head n} {X T : Tm Head n} (le : TypeLe S.R Γ X T)
    (typeT : IsType S.R Γ T) (formed : CtxFormed S.R Γ)
    (notUniverse : ∀ u, S.R.isUniverse u → ¬ TypeEq S.R Γ X (.head u))
    (notPi : ∀ A B, ¬ TypeEq S.R Γ X (.pi A B)) (notSigma : ∀ A B, ¬ TypeEq S.R Γ X (.sigma A B)) :
    TypeEq S.R Γ X T :=
  Below.rigid (TypeLe.toBelow le typeT) formed notUniverse notPi notSigma

/-- A chain from an identity type ends in a type equal to it. -/
theorem TypeLe.id_eq {n : Nat} {Γ : Ctx Head n} {C a b T : Tm Head n}
    (le : TypeLe S.R Γ (.id C a b) T) (typeT : IsType S.R Γ T) (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ (.id C a b) T :=
  TypeLe.rigid le typeT formed
    (fun _ _ e => TypeEq.id_ne_head facts formed e)
    (fun _ _ e => TypeEq.pi_ne_id facts formed e.symm)
    (fun _ _ e => TypeEq.sigma_ne_id facts formed e.symm)

end Inversion

/-! ## The contractions -/

section Contractions

variable (facts : FormFacts S.R S.roles)
include facts

theorem Typed.beta_preserve {n : Nat} {Γ : Ctx Head n} {a T : Tm Head n}
    {body : Tm Head (n + 1)} (formed : CtxFormed S.R Γ)
    (typing : Typed S.R Γ (.app (.lam body) a) T) :
    Typed S.R Γ (inst0 a body) T ∧ Equal S.R Γ (.app (.lam body) a) (inst0 a body) T := by
  obtain ⟨A, B, tf, ta, le⟩ := typing.generation
  have tb := Typed.lam_inv facts tf formed
  obtain ⟨w, hw, tPi⟩ := Typed.isType tf formed
  exact ⟨Typed.subsume (Typed.instantiate tb ta) le, Equal.subsume (Derivable.betaPi tPi hw tb ta) le⟩

theorem Typed.fstPair_preserve {n : Nat} {Γ : Ctx Head n} {a b T : Tm Head n}
    (formed : CtxFormed S.R Γ) (typing : Typed S.R Γ (.fst (.pair a b)) T) :
    Typed S.R Γ a T ∧ Equal S.R Γ (.fst (.pair a b)) a T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  obtain ⟨ta, tb⟩ := Typed.pair_inv facts tp formed
  obtain ⟨w, hw, tSigma⟩ := Typed.isType tp formed
  exact ⟨Typed.subsume ta le, Equal.subsume (Derivable.betaFst tSigma hw ta tb) le⟩

theorem Typed.sndPair_preserve {n : Nat} {Γ : Ctx Head n} {a b T : Tm Head n}
    (formed : CtxFormed S.R Γ) (typing : Typed S.R Γ (.snd (.pair a b)) T) :
    Typed S.R Γ b T ∧ Equal S.R Γ (.snd (.pair a b)) b T := by
  obtain ⟨A, B, tp, le⟩ := typing.generation
  obtain ⟨ta, tb⟩ := Typed.pair_inv facts tp formed
  have typeSigma := Typed.isType tp formed
  obtain ⟨w, hw, tSigma⟩ := typeSigma
  obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, tSigma⟩
  have change : TypeEq S.R Γ (inst0 a B) (inst0 (.fst (.pair a b)) B) :=
    TypeEq.of_instantiateEq family hv ta (.symm (.betaFst tSigma hw ta tb))
  exact ⟨Typed.subsume (Typed.convType tb change) le,
    Equal.subsume (Equal.convType (Derivable.betaSnd tSigma hw ta tb) change) le⟩

end Contractions

/-! ## Weak-head reduction -/

section WeakHead

variable (facts : FormFacts S.R S.roles)
include facts

omit facts in
/-- Replacing one argument of an application spine by a term that preserves its
typings, with an equality. -/
theorem Typed.spine_replace {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {f a a' : Tm Head n} {before : List (Tm Head n)}
    (replace : ∀ {T}, Typed S.R Γ a T → Typed S.R Γ a' T ∧ Equal S.R Γ a a' T) :
    ∀ (after : List (Tm Head n)) {T : Tm Head n},
      Typed S.R Γ (appSpine f (before ++ a :: after)) T →
      Typed S.R Γ (appSpine f (before ++ a' :: after)) T ∧
        Equal S.R Γ (appSpine f (before ++ a :: after)) (appSpine f (before ++ a' :: after)) T := by
  intro after
  induction after using List.reverseRecOn with
  | nil =>
      intro T typing
      rw [appSpine_concat] at typing ⊢
      rw [appSpine_concat]
      obtain ⟨A, B, tg, ta, le⟩ := typing.generation
      obtain ⟨ta', e⟩ := replace ta
      obtain ⟨w, hw, tPi⟩ := Typed.isType tg formed
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨w, hw, tPi⟩
      have change : TypeEq S.R Γ (inst0 a' B) (inst0 a B) :=
        TypeEq.symm (TypeEq.of_instantiateEq family hv ta e)
      exact ⟨Typed.subsume (Typed.convType (Derivable.appElim tg ta') change) le,
        Equal.subsume (Derivable.appCong (.refl tg) e) le⟩
  | append_singleton init x ih =>
      intro T typing
      have shape : ∀ c : Tm Head n, before ++ c :: (init ++ [x]) = (before ++ c :: init) ++ [x] := by
        intro c; simp
      rw [shape a, appSpine_concat] at typing
      rw [shape a, shape a', appSpine_concat, appSpine_concat]
      obtain ⟨A, B, tg, tx, le⟩ := typing.generation
      obtain ⟨tg', e⟩ := ih tg
      exact ⟨Typed.subsume (Derivable.appElim tg' tx) le, Equal.subsume (Derivable.appCong e (.refl tx)) le⟩

omit facts in
/-- Replacing the point of a reflexivity by a term that preserves its
typings, with an equality. -/
theorem Typed.refl_replace {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {a a' : Tm Head n}
    (replace : ∀ {T}, Typed S.R Γ a T → Typed S.R Γ a' T ∧ Equal S.R Γ a a' T)
    {T : Tm Head n} (typing : Typed S.R Γ (.refl a) T) :
    Typed S.R Γ (.refl a') T ∧ Equal S.R Γ (.refl a) (.refl a') T := by
  obtain ⟨A, ta, le⟩ := typing.generation
  obtain ⟨_, e⟩ := replace ta
  have equal : Equal S.R Γ (.refl a) (.refl a') (.id A a a) := Derivable.reflCong e
  exact ⟨Typed.subsume (Equal.typed equal formed).2 le, Equal.subsume equal le⟩

/-- Weak-head steps preserve typing and are typed equalities. -/
theorem WhStep.preserve (roots : RootPreserving S.R) {n : Nat} {t t' : Tm Head n}
    (step : WhStep S.R S.roles t t') :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → ∀ {T : Tm Head n}, Typed S.R Γ t T →
      Typed S.R Γ t' T ∧ Equal S.R Γ t t' T := by
  induction step with
  | beta body a => exact fun formed _ typing => Typed.beta_preserve facts formed typing
  | fstPair a b => exact fun formed _ typing => Typed.fstPair_preserve facts formed typing
  | sndPair a b => exact fun formed _ typing => Typed.sndPair_preserve facts formed typing
  | root st =>
      intro Γ formed T typing
      exact ⟨roots formed st typing, .root st typing (roots formed st typing)⟩
  | appFun _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := typing.generation
      obtain ⟨tf', e⟩ := ih formed tf
      exact ⟨Typed.subsume (Derivable.appElim tf' ta) le, Equal.subsume (Derivable.appCong e (.refl ta)) le⟩
  | fst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      obtain ⟨tp', e⟩ := ih formed tp
      exact ⟨Typed.subsume (Derivable.fstElim tp') le, Equal.subsume (Derivable.fstCong e) le⟩
  | snd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := typing.generation
      obtain ⟨tp', e⟩ := ih formed tp
      obtain ⟨w, hw, tSigma⟩ := Typed.isType tp formed
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, tSigma⟩
      have change := (TypeEq.of_instantiateEq family hv (.fstElim tp) (.fstCong e)).symm
      exact ⟨Typed.subsume (Typed.convType (Derivable.sndElim tp') change) le,
        Equal.subsume (Derivable.sndCong e) le⟩
  | scrutinee _ _ focus _ ih =>
      intro Γ formed T typing
      obtain ⟨before, after, x, y, rfl, rfl, replace⟩ := focus.lift
        (r := fun x y => ∀ {T}, Typed S.R Γ x T → Typed S.R Γ y T ∧ Equal S.R Γ x y T)
        (fun _ before after {_ _} step {_} typing =>
          Typed.spine_replace (before := before) formed step after typing)
        (fun {_ _} step {_} typing => Typed.refl_replace formed step typing)
        (fun {_} typing => ih formed typing)
      exact Typed.spine_replace formed replace after typing

/-- Weak-head reduction preserves typing and is a typed equality. -/
theorem WhRed.preserve (roots : RootPreserving S.R) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) {t t' T : Tm Head n} (red : WhRed S.R S.roles t t')
    (typing : Typed S.R Γ t T) : Typed S.R Γ t' T ∧ Equal S.R Γ t t' T := by
  induction red with
  | refl => exact ⟨typing, .refl typing⟩
  | tail _ step ih =>
      obtain ⟨typing', e⟩ := ih
      obtain ⟨typing'', e'⟩ := WhStep.preserve facts roots step formed typing'
      exact ⟨typing'', .trans e e'⟩

end WeakHead

/-! ## Contextual steps -/

section Contextual

variable (facts : FormFacts S.R S.roles)
include facts

/-- Contextual steps of the rule package preserve typing and are typed
equalities. -/
theorem StepCore.preserve (roots : RootPreserving S.R) (heads : HeadPreserving S.R) {n : Nat}
    {t t' : Tm Head n} (step : StepCore S.R.computation S.R.headEq t t') :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → ∀ {T : Tm Head n}, Typed S.R Γ t T →
      Typed S.R Γ t' T ∧ Equal S.R Γ t t' T := by
  induction step with
  | betaPi body a => exact fun formed _ typing => Typed.beta_preserve facts formed typing
  | betaSigmaFst a b =>
      exact fun formed _ typing => Typed.fstPair_preserve facts formed typing
  | betaSigmaSnd a b =>
      exact fun formed _ typing => Typed.sndPair_preserve facts formed typing
  | head same =>
      intro Γ formed T typing
      have typing' := heads same typing
      exact ⟨typing', .headEq same typing typing'⟩
  | root st =>
      intro Γ formed T typing
      exact ⟨roots formed st typing, .root st typing (roots formed st typing)⟩
  | congPiDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := Typed.generation typing
      obtain ⟨tA', e⟩ := ih formed tA
      have tB' := Typed.ctxConv tB ⟨u, hu, e⟩
      exact ⟨Typed.subsume (.piForm tA' hu tB' hv join) le,
        Equal.subsume (.piCong e hu (.refl tB) hv join) le⟩
  | congPiCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := Typed.generation typing
      obtain ⟨tB', e⟩ := ih (.snoc formed ⟨u, hu, tA⟩) tB
      exact ⟨Typed.subsume (.piForm tA hu tB' hv join) le,
        Equal.subsume (.piCong (.refl tA) hu e hv join) le⟩
  | congSigmaDom _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := Typed.generation typing
      obtain ⟨tA', e⟩ := ih formed tA
      have tB' := Typed.ctxConv tB ⟨u, hu, e⟩
      exact ⟨Typed.subsume (.sigmaForm tA' hu tB' hv join) le,
        Equal.subsume (.sigmaCong e hu (.refl tB) hv join) le⟩
  | congSigmaCod _ ih =>
      intro Γ formed T typing
      obtain ⟨u, v, w, tA, hu, tB, hv, join, le⟩ := Typed.generation typing
      obtain ⟨tB', e⟩ := ih (.snoc formed ⟨u, hu, tA⟩) tB
      exact ⟨Typed.subsume (.sigmaForm tA hu tB' hv join) le,
        Equal.subsume (.sigmaCong (.refl tA) hu e hv join) le⟩
  | congIdTy _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := Typed.generation typing
      obtain ⟨tA', e⟩ := ih formed tA
      have equal : TypeEq S.R Γ _ _ := ⟨u, hu, e⟩
      exact ⟨Typed.subsume (.idForm tA' hu (Typed.convType ta equal) (Typed.convType tb equal)) le,
        Equal.subsume (.idCong e hu (.refl ta) (.refl tb)) le⟩
  | congIdLeft _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := Typed.generation typing
      obtain ⟨ta', e⟩ := ih formed ta
      exact ⟨Typed.subsume (.idForm tA hu ta' tb) le,
        Equal.subsume (.idCong (.refl tA) hu e (.refl tb)) le⟩
  | congIdRight _ ih =>
      intro Γ formed T typing
      obtain ⟨u, tA, hu, ta, tb, le⟩ := Typed.generation typing
      obtain ⟨tb', e⟩ := ih formed tb
      exact ⟨Typed.subsume (.idForm tA hu ta tb') le,
        Equal.subsume (.idCong (.refl tA) hu (.refl ta) e) le⟩
  | congLam _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tPi, hu, tb, le⟩ := Typed.generation typing
      obtain ⟨⟨u', hu', tA⟩, _⟩ := IsType.pi_parts ⟨u, hu, tPi⟩
      obtain ⟨tb', e⟩ := ih (.snoc formed ⟨u', hu', tA⟩) tb
      exact ⟨Typed.subsume (.lamIntro tPi hu tb') le, Equal.subsume (.lamCong tPi hu e) le⟩
  | congAppFun _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := Typed.generation typing
      obtain ⟨tf', e⟩ := ih formed tf
      exact ⟨Typed.subsume (.appElim tf' ta) le, Equal.subsume (.appCong e (.refl ta)) le⟩
  | congAppArg _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tf, ta, le⟩ := Typed.generation typing
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨w, hw, tPi⟩ := Typed.isType tf formed
      obtain ⟨_, v, hv, family⟩ := IsType.pi_parts ⟨w, hw, tPi⟩
      have change := TypeEq.symm (TypeEq.of_instantiateEq family hv ta e)
      exact ⟨Typed.subsume (Typed.convType (.appElim tf ta') change) le,
        Equal.subsume (.appCong (.refl tf) e) le⟩
  | congPairFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := Typed.generation typing
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨u, hu, tSigma⟩
      have change := TypeEq.of_instantiateEq family hv ta e
      exact ⟨Typed.subsume (.pairIntro tSigma hu ta' (Typed.convType tb change)) le,
        Equal.subsume (.pairCong tSigma hu e (.refl tb)) le⟩
  | congPairSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, u, tSigma, hu, ta, tb, le⟩ := Typed.generation typing
      obtain ⟨tb', e⟩ := ih formed tb
      exact ⟨Typed.subsume (.pairIntro tSigma hu ta tb') le,
        Equal.subsume (.pairCong tSigma hu (.refl ta) e) le⟩
  | congFst _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := Typed.generation typing
      obtain ⟨tp', e⟩ := ih formed tp
      exact ⟨Typed.subsume (.fstElim tp') le, Equal.subsume (.fstCong e) le⟩
  | congSnd _ ih =>
      intro Γ formed T typing
      obtain ⟨A, B, tp, le⟩ := Typed.generation typing
      obtain ⟨tp', e⟩ := ih formed tp
      obtain ⟨w, hw, tSigma⟩ := Typed.isType tp formed
      obtain ⟨_, v, hv, family⟩ := IsType.sigma_parts ⟨w, hw, tSigma⟩
      have change := TypeEq.symm (TypeEq.of_instantiateEq family hv (.fstElim tp) (.fstCong e))
      exact ⟨Typed.subsume (Typed.convType (.sndElim tp') change) le,
        Equal.subsume (.sndCong e) le⟩
  | congRefl _ ih =>
      intro Γ formed T typing
      obtain ⟨A, ta, le⟩ := Typed.generation typing
      obtain ⟨ta', e⟩ := ih formed ta
      obtain ⟨u, hu, tA⟩ := Typed.isType ta formed
      have change : TypeEq S.R Γ (.id A _ _) (.id A _ _) :=
        ⟨u, hu, .idCong (.refl tA) hu (.symm e) (.symm e)⟩
      exact ⟨Typed.subsume (Typed.convType (.reflIntro ta') change) le,
        Equal.subsume (.reflCong e) le⟩

/-- Reduction of the rule package preserves typing and is a typed equality. -/
theorem Reduces.preserve (roots : RootPreserving S.R) (heads : HeadPreserving S.R) {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t t' T : Tm Head n} (red : Reduces S.R t t')
    (typing : Typed S.R Γ t T) : Typed S.R Γ t' T ∧ Equal S.R Γ t t' T := by
  induction red with
  | refl => exact ⟨typing, .refl typing⟩
  | tail _ step ih =>
      obtain ⟨typing', e⟩ := ih
      obtain ⟨typing'', e'⟩ := StepCore.preserve facts roots heads step formed typing'
      exact ⟨typing'', .trans e e'⟩

end Contextual

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
