import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Coherence

/-!
# Lifting derivations to the annotation: the Church–Curry correspondence

Annotated derivations erase to derivations of the rule package (`CDerivable.erase`). This
module proves the converse, for every annotation of a rule package with the four properties
bundled in `LiftingFacts`:

* **coherence** of annotations: two annotated terms with one erasure, typed at one type in
  one formed context, are equal at it;
* **root lifting**: every root step of the erasure of an annotated term is the erasure of an
  annotated root step of that term;
* **root steps as equalities**: an annotated root step of a typed term of a formed context
  is an equality at its type (`CRootAdmitted`);
* **formed declarations**: an annotated declared type is a type as soon as some annotation of
  its erasure is (`CDeclsFormed`). It holds when the declared types are types
  (`declsFormed_of_isType`), and when each is the only annotation of its erasure
  (`CDeclsRigid.formed`), as declared types without abstractions are (`rigid_of_lamFree`).

**Lifting** (`lifts`): every derivation of the rule package whose context is the erasure of a
formed annotated context is the erasure of an annotated derivation over that annotated
context. The annotated context is chosen by the caller; the annotated terms and types are
chosen by the proof, rule by rule:

* a type former, an introduction or an elimination is lifted from the lifts of its premises,
  whose types are re-anchored at the types the rule needs. Two annotated types of one formed
  context with one erasure are equal (`LiftingFacts.typeEq`): both are raised to the join of
  their universes, and coherence compares them there;
* an abstraction takes the domain of the lifted dependent function type it is checked at, so
  the domain of every abstraction is reconstructed from a type, not read off the raw term;
* where two premises lift one raw term twice (transitivity, the η-rules, the middle type of a
  subtyping chain), coherence equates the two lifts;
* a root step is lifted by root lifting, and is an equality at the type of its left side;
* a constant is typed at its annotated declared type, which is a type because the raw
  typing of its raw declared type lifts.

The syntactic validity of the annotated judgment, context conversion, and substitution by
typed substitutions supply the typings the re-anchoring needs.

**Contexts** (`lift_ctxFormed`): a formed context is the erasure of a formed annotated
context. Together, lifting and contexts give the two forms the transfer of the facts about
weak-head forms consumes: types lift (`lift_isType`) and equations of types lift
(`lift_typeEq`), each over a formed annotated context erasing to the given one.

**Rigid terms** (`CTm.eq_liftTm_of_lamFree`): a term whose erasure has no abstraction is the
annotation of that erasure without domains.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (LevelModel IsType TypeEq CtxFormed)
open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-! ## Rigid terms -/

/-- **A term whose erasure has no abstraction is the only annotation of its erasure.** -/
theorem CTm.eq_liftTm_of_lamFree {n : Nat} {t : CTm Head n} (lf : lamFree t.erase = true) :
    t = liftTm t.erase := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [CTm.erase, lamFree, Bool.and_eq_true] at lf
      show CTm.pi A B = CTm.pi (liftTm A.erase) (liftTm B.erase)
      rw [← ihA lf.1, ← ihB lf.2]
  | sigma A B ihA ihB =>
      simp only [CTm.erase, lamFree, Bool.and_eq_true] at lf
      show CTm.sigma A B = CTm.sigma (liftTm A.erase) (liftTm B.erase)
      rw [← ihA lf.1, ← ihB lf.2]
  | id A a b ihA iha ihb =>
      simp only [CTm.erase, lamFree, Bool.and_eq_true] at lf
      show CTm.id A a b = CTm.id (liftTm A.erase) (liftTm a.erase) (liftTm b.erase)
      rw [← ihA lf.1.1, ← iha lf.1.2, ← ihb lf.2]
  | lam A b _ _ => simp [CTm.erase, lamFree] at lf
  | app f a ihf iha =>
      simp only [CTm.erase, lamFree, Bool.and_eq_true] at lf
      show CTm.app f a = CTm.app (liftTm f.erase) (liftTm a.erase)
      rw [← ihf lf.1, ← iha lf.2]
  | pair a b iha ihb =>
      simp only [CTm.erase, lamFree, Bool.and_eq_true] at lf
      show CTm.pair a b = CTm.pair (liftTm a.erase) (liftTm b.erase)
      rw [← iha lf.1, ← ihb lf.2]
  | fst p ih =>
      simp only [CTm.erase, lamFree] at lf
      show CTm.fst p = CTm.fst (liftTm p.erase)
      rw [← ih lf]
  | snd p ih =>
      simp only [CTm.erase, lamFree] at lf
      show CTm.snd p = CTm.snd (liftTm p.erase)
      rw [← ih lf]
  | refl a ih =>
      simp only [CTm.erase, lamFree] at lf
      show CTm.refl a = CTm.refl (liftTm a.erase)
      rw [← ih lf]

/-- Two annotated terms with one erasure without abstractions are equal. -/
theorem CTm.eq_of_erase_eq_of_lamFree {n : Nat} {s t : CTm Head n} (same : s.erase = t.erase)
    (lf : lamFree t.erase = true) : s = t :=
  calc s = liftTm s.erase := CTm.eq_liftTm_of_lamFree (same ▸ lf)
    _ = liftTm t.erase := by rw [same]
    _ = t := (CTm.eq_liftTm_of_lamFree lf).symm

/-! ## Declared types -/

/-- **The annotated declared types are formed as soon as their erasures are**: an annotated
declared type is a type of the empty context whenever some annotation of its erasure is. -/
def CDeclsFormed (P : ChurchRules R) : Prop :=
  ∀ {name : DeclName} {type T : CTm Head 0} {u : Head}, P.constantType name = some type →
    T.erase = type.erase → CTyped P .nil T (.head u) → R.isUniverse u →
      ∃ v, R.isUniverse v ∧ CTyped P .nil type (.head v)

/-- Declared types that are types are formed as soon as their erasures are. -/
theorem declsFormed_of_isType {P : ChurchRules R}
    (typed : ∀ {name : DeclName} {type : CTm Head 0}, P.constantType name = some type →
      CIsType P .nil type) : CDeclsFormed P :=
  fun declared _ _ _ => typed declared

/-- An annotated declared type is **rigid** when it is the only annotation of its erasure. -/
def CDeclsRigid (P : ChurchRules R) : Prop :=
  ∀ {name : DeclName} {type T : CTm Head 0}, P.constantType name = some type →
    T.erase = type.erase → T = type

/-- Rigid declared types are formed as soon as their erasures are. -/
theorem CDeclsRigid.formed {P : ChurchRules R} (rigid : CDeclsRigid P) : CDeclsFormed P :=
  fun declared same typing hu => ⟨_, hu, rigid declared same ▸ typing⟩

/-- Declared types whose erasures have no abstraction are rigid. -/
theorem rigid_of_lamFree {P : ChurchRules R}
    (lf : ∀ {name : DeclName} {type : CTm Head 0}, P.constantType name = some type →
      lamFree type.erase = true) : CDeclsRigid P :=
  fun declared same => CTm.eq_of_erase_eq_of_lamFree same (lf declared)

/-! ## The facts lifting needs -/

/-- **The facts lifting derivations to an annotation needs**: coherence of annotations at
one type, root lifting, root steps that are equalities, and formed declared types. -/
structure LiftingFacts (P : ChurchRules R) : Prop where
  /-- Coherence of annotations: two annotated terms with one erasure, typed at one type in
  one formed context, are equal at it. -/
  coherent : ∀ {n : Nat} {Γ : CCtx Head n} {t t' A : CTm Head n}, CCtxFormed P Γ →
    CTyped P Γ t A → CTyped P Γ t' A → t.erase = t'.erase → CEqual P Γ t t' A
  /-- Root lifting: a root step of an erasure is the erasure of an annotated root step. -/
  lift : ∀ {n : Nat} {l : CTm Head n} {r : Tm Head n}, R.computation.step l.erase r →
    ∃ r', P.computation.step l r' ∧ r'.erase = r
  /-- Annotated root steps of typed terms are equalities. -/
  admitted : CRootAdmitted P
  /-- Annotated declared types are formed as soon as their erasures are. -/
  declared : CDeclsFormed P

/-- The facts, from the facts coherence is proved from and the universe laws. -/
theorem LiftingFacts.ofCoherenceFacts {P : ChurchRules R} (facts : CoherenceFacts P)
    (levels : LevelModel R L) (algebra : Normalization.CumulativeAlgebra R)
    (lift : ∀ {n : Nat} {l : CTm Head n} {r : Tm Head n}, R.computation.step l.erase r →
      ∃ r', P.computation.step l r' ∧ r'.erase = r)
    (admitted : CRootAdmitted P) (declared : CDeclsFormed P) : LiftingFacts P where
  coherent formed typing typing' same := coherence facts levels algebra formed typing typing' same
  lift := lift
  admitted := admitted
  declared := declared

/-! ## Re-anchoring lifts at a type -/

section Anchoring

variable {P : ChurchRules R} (levels : LevelModel R L) (facts : LiftingFacts P)
include levels facts

/-- **Two types of a formed context with one erasure are equal**: both are raised to the
join of their universes, and coherence compares them there. -/
theorem LiftingFacts.typeEq {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {A B : CTm Head n} (typeA : CIsType P Γ A) (typeB : CIsType P Γ B)
    (same : A.erase = B.erase) : CTypeEq P Γ A B := by
  obtain ⟨u, hu, tA⟩ := typeA
  obtain ⟨v, hv, tB⟩ := typeB
  obtain ⟨w, join⟩ := levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := levels.join_upper join
  exact ⟨w, (levels.join_level join).1,
    facts.coherent formed (CDerivable.cumul tA uw) (CDerivable.cumul tB vw) same⟩

/-- A typed term is typed at every type with the erasure of its type. -/
theorem LiftingFacts.retype {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {t A B : CTm Head n} (typing : CTyped P Γ t A) (typeB : CIsType P Γ B)
    (same : A.erase = B.erase) : CTyped P Γ t B :=
  CTyped.convType typing
    (facts.typeEq levels formed (CTyped.isType levels typing formed) typeB same)

/-- An equality holds at every type with the erasure of its type. -/
theorem LiftingFacts.reequal {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ)
    {a b A B : CTm Head n} (equal : CEqual P Γ a b A) (typeB : CIsType P Γ B)
    (same : A.erase = B.erase) : CEqual P Γ a b B :=
  CEqual.convType equal
    (facts.typeEq levels formed (CDerivable.presupposed levels equal formed).2.2 typeB same)

end Anchoring

/-! ## Lifting -/

/-- **What lifting gives for a statement of the rule package**: over every formed annotated
context erasing to the statement's context, an annotated statement of that context erasing
to it is derivable. -/
abbrev Lifts (P : ChurchRules R) : Statement Head → Prop
  | .typing Γ t A => ∀ {Γ' : CCtx Head _}, CCtxFormed P Γ' → Γ'.erase = Γ →
      ∃ t' A', t'.erase = t ∧ A'.erase = A ∧ CTyped P Γ' t' A'
  | .equality Γ a b A => ∀ {Γ' : CCtx Head _}, CCtxFormed P Γ' → Γ'.erase = Γ →
      ∃ a' b' A', a'.erase = a ∧ b'.erase = b ∧ A'.erase = A ∧ CEqual P Γ' a' b' A'
  | .sub Γ A B => ∀ {Γ' : CCtx Head _}, CCtxFormed P Γ' → Γ'.erase = Γ →
      ∃ A' B', A'.erase = A ∧ B'.erase = B ∧ CBelow P Γ' A' B'

section Lifting

variable {P : ChurchRules R} (levels : LevelModel R L) (facts : LiftingFacts P)
include levels facts

/-- **Lifting**: every derivation of the rule package lifts to the annotation, over every
formed annotated context erasing to its context. -/
theorem lifts {statement : Statement Head} (derivation : Derivable R statement) :
    Lifts P statement := by
  induction derivation with
  | headType h =>
      intro Γ' _ _
      exact ⟨.head _, .head _, rfl, rfl, .headType h⟩
  | var i =>
      intro Γ' _ eΓ
      subst eΓ
      exact ⟨.var i, Γ'.lookup i, rfl, CCtx.erase_lookup Γ' i, .var i⟩
  | @const n Γ name type u declared _ hu ih =>
      intro Γ' _ _
      obtain ⟨T, U, eT, eU, tT⟩ := ih CCtxFormed.nil rfl
      obtain rfl := CTm.erase_eq_head eU
      have hmap := P.erase_constantType name
      rw [declared] at hmap
      cases hP : P.constantType name with
      | none =>
          rw [hP] at hmap
          cases hmap
      | some type' =>
          rw [hP, Option.map_some] at hmap
          have etype : type'.erase = type := Option.some.inj hmap
          obtain ⟨v, hv, tT'⟩ := facts.declared hP (eT.trans etype.symm) tT hu
          exact ⟨.const name, type'.liftClosed, rfl, by rw [CTm.erase_liftClosed, etype],
            .const hP tT' hv⟩
  | piForm _ hu _ hv join ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, U, eA, eU, tA⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA
      obtain ⟨B₁, V, eB, eV, tB⟩ := ihB (.snoc formed ⟨_, hu, tA⟩) rfl
      obtain rfl := CTm.erase_eq_head eV
      subst eB
      exact ⟨.pi A₁ B₁, .head _, rfl, rfl, .piForm tA hu tB hv join⟩
  | sigmaForm _ hu _ hv join ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, U, eA, eU, tA⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA
      obtain ⟨B₁, V, eB, eV, tB⟩ := ihB (.snoc formed ⟨_, hu, tA⟩) rfl
      obtain rfl := CTm.erase_eq_head eV
      subst eB
      exact ⟨.sigma A₁ B₁, .head _, rfl, rfl, .sigmaForm tA hu tB hv join⟩
  | lamIntro _ hu _ ihPi ihBody =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihPi formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eS
      obtain ⟨⟨w, hw, tA⟩, typeB⟩ := CIsType.pi_parts ⟨_, hu, tS⟩
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed ⟨w, hw, tA⟩
      obtain ⟨b₁, B₂, eb, eB, tb⟩ := ihBody formed' rfl
      subst eb
      exact ⟨.lam A₁ b₁, .pi A₁ B₁, rfl, rfl,
        .lamIntro tA hw tS hu (facts.retype levels formed' tb typeB eB)⟩
  | appElim _ _ ihF ihA =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨g₁, T, eg, eT, tg⟩ := ihF formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eT
      subst eg
      obtain ⟨a₁, A₂, ea, eA, ta⟩ := ihA formed rfl
      subst ea
      have typeA := (CIsType.pi_parts (CTyped.isType levels tg formed)).1
      exact ⟨.app g₁ a₁, CTm.inst0 a₁ B₁, rfl, CTm.erase_inst0 a₁ B₁,
        .appElim tg (facts.retype levels formed ta typeA eA)⟩
  | pairIntro _ hu _ _ ihS iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihS formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS
      obtain ⟨typeA, v, hv, tB⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨a₁, A₂, ea, eA, ta⟩ := iha formed rfl
      subst ea
      have ta' := facts.retype levels formed ta typeA eA
      obtain ⟨b₁, C, eb, eC, tb⟩ := ihb formed rfl
      subst eb
      have tb' := facts.retype levels formed tb ⟨v, hv, CTyped.instantiate tB ta'⟩
        (eC.trans (CTm.erase_inst0 a₁ B₁).symm)
      exact ⟨.pair a₁ b₁, .sigma A₁ B₁, rfl, rfl, .pairIntro tS hu ta' tb'⟩
  | fstElim _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨p₁, T, ep, eT, tp⟩ := ih formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eT
      subst ep
      exact ⟨.fst p₁, A₁, rfl, rfl, .fstElim tp⟩
  | sndElim _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨p₁, T, ep, eT, tp⟩ := ih formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eT
      subst ep
      exact ⟨.snd p₁, CTm.inst0 (.fst p₁) B₁, rfl, CTm.erase_inst0 (.fst p₁) B₁, .sndElim tp⟩
  | idForm _ hu _ _ ihA iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, U, eA, eU, tA⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA
      obtain ⟨a₁, A₂, ea, eA₂, ta⟩ := iha formed rfl
      obtain ⟨b₁, A₃, eb, eA₃, tb⟩ := ihb formed rfl
      subst ea eb
      exact ⟨.id A₁ a₁ b₁, .head _, rfl, rfl,
        .idForm tA hu (facts.retype levels formed ta ⟨_, hu, tA⟩ eA₂)
          (facts.retype levels formed tb ⟨_, hu, tA⟩ eA₃)⟩
  | reflIntro _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨a₁, A₁, ea, eA, ta⟩ := ih formed rfl
      subst ea eA
      exact ⟨.refl a₁, .id A₁ a₁ a₁, rfl, rfl, .reflIntro ta⟩
  | sub _ _ ihT ihLe =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨t₁, A₁, et, eA, tt⟩ := ihT formed rfl
      obtain ⟨A₂, B₂, eA₂, eB, le⟩ := ihLe formed rfl
      subst et eA eB
      exact ⟨t₁, B₂, rfl, rfl,
        .sub (facts.retype levels formed tt (CBelow.isTypes levels le formed).1 eA₂.symm) le⟩
  | conv _ _ hu ihT ihE =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨t₁, A₁, et, eA, tt⟩ := ihT formed rfl
      obtain ⟨A₂, B₂, U, eA₂, eB, eU, e⟩ := ihE formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst et eA eB
      exact ⟨t₁, B₂, rfl, rfl,
        .conv (facts.retype levels formed tt ⟨_, hu, (CEqual.typed levels e formed).1⟩ eA₂.symm)
          e hu⟩
  | refl _ ih =>
      intro Γ' formed eΓ
      obtain ⟨a₁, A₁, ea, eA, ta⟩ := ih formed eΓ
      exact ⟨a₁, a₁, A₁, ea, ea, eA, .refl ta⟩
  | symm _ ih =>
      intro Γ' formed eΓ
      obtain ⟨a₁, b₁, A₁, ea, eb, eA, e⟩ := ih formed eΓ
      exact ⟨b₁, a₁, A₁, eb, ea, eA, .symm e⟩
  | trans _ _ ih₁ ih₂ =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨a₁, b₁, A₁, ea, eb, eA, e₁⟩ := ih₁ formed rfl
      obtain ⟨b₂, c₂, A₂, eb₂, ec, eA₂, e₂⟩ := ih₂ formed rfl
      subst ea eb eA ec
      have e₂' := facts.reequal levels formed e₂ (CDerivable.presupposed levels e₁ formed).2.2 eA₂
      have middle := facts.coherent formed (CEqual.typed levels e₁ formed).2
        (CEqual.typed levels e₂' formed).1 eb₂.symm
      exact ⟨a₁, c₂, A₁, rfl, rfl, rfl, .trans e₁ (.trans middle e₂')⟩
  | convEq _ _ hu ih ihE =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨a₁, b₁, A₁, ea, eb, eA, e⟩ := ih formed rfl
      obtain ⟨A₂, B₂, U, eA₂, eB, eU, eAB⟩ := ihE formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA eB
      exact ⟨a₁, b₁, B₂, ea, eb, rfl,
        .convEq (facts.reequal levels formed e ⟨_, hu, (CEqual.typed levels eAB formed).1⟩
          eA₂.symm) eAB hu⟩
  | subEq _ _ ih ihLe =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨a₁, b₁, A₁, ea, eb, eA, e⟩ := ih formed rfl
      obtain ⟨A₂, B₂, eA₂, eB, le⟩ := ihLe formed rfl
      subst eA eB
      exact ⟨a₁, b₁, B₂, ea, eb, rfl,
        .subEq (facts.reequal levels formed e (CBelow.isTypes levels le formed).1 eA₂.symm) le⟩
  | headEq he _ _ ih ih' =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨x, A₁, ex, eA, th⟩ := ih formed rfl
      obtain ⟨x', A₂, ex', eA₂, th'⟩ := ih' formed rfl
      obtain rfl := CTm.erase_eq_head ex
      obtain rfl := CTm.erase_eq_head ex'
      subst eA
      exact ⟨.head _, .head _, A₁, rfl, rfl, rfl,
        .headEq he th (facts.retype levels formed th' (CTyped.isType levels th formed) eA₂)⟩
  | piCong _ hu _ hv join ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, A₁', U, eA, eA', eU, e⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA eA'
      obtain ⟨B₁, B₁', V, eB, eB', eV, eBB⟩ :=
        ihB (.snoc formed ⟨_, hu, (CEqual.typed levels e formed).1⟩) rfl
      obtain rfl := CTm.erase_eq_head eV
      subst eB eB'
      exact ⟨.pi A₁ B₁, .pi A₁' B₁', .head _, rfl, rfl, rfl, .piCong e hu eBB hv join⟩
  | sigmaCong _ hu _ hv join ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, A₁', U, eA, eA', eU, e⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA eA'
      obtain ⟨B₁, B₁', V, eB, eB', eV, eBB⟩ :=
        ihB (.snoc formed ⟨_, hu, (CEqual.typed levels e formed).1⟩) rfl
      obtain rfl := CTm.erase_eq_head eV
      subst eB eB'
      exact ⟨.sigma A₁ B₁, .sigma A₁' B₁', .head _, rfl, rfl, rfl, .sigmaCong e hu eBB hv join⟩
  | idCong _ hu _ _ ihA iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, A₁', U, eA, eA', eU, e⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eU
      subst eA eA'
      have typeA : CIsType P Γ' A₁ := ⟨_, hu, (CEqual.typed levels e formed).1⟩
      obtain ⟨a₁, a₁', A₂, ea, ea', eA₂, e₁⟩ := iha formed rfl
      obtain ⟨b₁, b₁', A₃, eb, eb', eA₃, e₂⟩ := ihb formed rfl
      subst ea ea' eb eb'
      exact ⟨.id A₁ a₁ b₁, .id A₁' a₁' b₁', .head _, rfl, rfl, rfl,
        .idCong e hu (facts.reequal levels formed e₁ typeA eA₂)
          (facts.reequal levels formed e₂ typeA eA₃)⟩
  | lamCong _ hu _ ihPi ihBody =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihPi formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eS
      obtain ⟨⟨w, hw, tA⟩, typeB⟩ := CIsType.pi_parts ⟨_, hu, tS⟩
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed ⟨w, hw, tA⟩
      obtain ⟨b₁, b₁', B₂, eb, eb', eB, e⟩ := ihBody formed' rfl
      subst eb eb'
      exact ⟨.lam A₁ b₁, .lam A₁ b₁', .pi A₁ B₁, rfl, rfl, rfl,
        .lamCong (.refl tA) hw tS hu (facts.reequal levels formed' e typeB eB)⟩
  | appCong _ _ ihF ihA =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨f₁, g₁, T, ef, eg, eT, e⟩ := ihF formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eT
      subst ef eg
      obtain ⟨a₁, b₁, A₂, ea, eb, eA, e'⟩ := ihA formed rfl
      subst ea eb
      have typeA := (CIsType.pi_parts (CDerivable.presupposed levels e formed).2.2).1
      exact ⟨.app f₁ a₁, .app g₁ b₁, CTm.inst0 a₁ B₁, rfl, rfl, CTm.erase_inst0 a₁ B₁,
        .appCong e (facts.reequal levels formed e' typeA eA)⟩
  | pairCong _ hu _ _ ihS iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihS formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS
      obtain ⟨typeA, v, hv, tB⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨a₁, a₁', A₂, ea, ea', eA, e₁⟩ := iha formed rfl
      subst ea ea'
      have e₁' := facts.reequal levels formed e₁ typeA eA
      obtain ⟨b₁, b₁', C, eb, eb', eC, e₂⟩ := ihb formed rfl
      subst eb eb'
      have e₂' := facts.reequal levels formed e₂
        ⟨v, hv, CTyped.instantiate tB (CEqual.typed levels e₁' formed).1⟩
        (eC.trans (CTm.erase_inst0 a₁ B₁).symm)
      exact ⟨.pair a₁ b₁, .pair a₁' b₁', .sigma A₁ B₁, rfl, rfl, rfl, .pairCong tS hu e₁' e₂'⟩
  | fstCong _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨p₁, q₁, T, ep, eq, eT, e⟩ := ih formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eT
      subst ep eq
      exact ⟨.fst p₁, .fst q₁, A₁, rfl, rfl, rfl, .fstCong e⟩
  | sndCong _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨p₁, q₁, T, ep, eq, eT, e⟩ := ih formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eT
      subst ep eq
      exact ⟨.snd p₁, .snd q₁, CTm.inst0 (.fst p₁) B₁, rfl, rfl,
        CTm.erase_inst0 (.fst p₁) B₁, .sndCong e⟩
  | reflCong _ ih =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨a₁, b₁, A₁, ea, eb, eA, e⟩ := ih formed rfl
      subst ea eb eA
      exact ⟨.refl a₁, .refl b₁, .id A₁ a₁ a₁, rfl, rfl, rfl, .reflCong e⟩
  | betaPi _ hu _ _ ihPi ihBody iha =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihPi formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eS
      obtain ⟨⟨w, hw, tA⟩, typeB⟩ := CIsType.pi_parts ⟨_, hu, tS⟩
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed ⟨w, hw, tA⟩
      obtain ⟨b₁, B₂, eb, eB, tb⟩ := ihBody formed' rfl
      subst eb
      obtain ⟨a₁, A₂, ea, eA, ta⟩ := iha formed rfl
      subst ea
      exact ⟨.app (.lam A₁ b₁) a₁, CTm.inst0 a₁ b₁, CTm.inst0 a₁ B₁, rfl,
        CTm.erase_inst0 a₁ b₁, CTm.erase_inst0 a₁ B₁,
        .betaPi tS hu (facts.retype levels formed' tb typeB eB)
          (facts.retype levels formed ta ⟨w, hw, tA⟩ eA)⟩
  | betaFst _ hu _ _ ihS iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihS formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS
      obtain ⟨typeA, v, hv, tB⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨a₁, A₂, ea, eA, ta⟩ := iha formed rfl
      subst ea
      have ta' := facts.retype levels formed ta typeA eA
      obtain ⟨b₁, C, eb, eC, tb⟩ := ihb formed rfl
      subst eb
      have tb' := facts.retype levels formed tb ⟨v, hv, CTyped.instantiate tB ta'⟩
        (eC.trans (CTm.erase_inst0 a₁ B₁).symm)
      exact ⟨.fst (.pair a₁ b₁), a₁, A₁, rfl, rfl, rfl, .betaFst tS hu ta' tb'⟩
  | betaSnd _ hu _ _ ihS iha ihb =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihS formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS
      obtain ⟨typeA, v, hv, tB⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨a₁, A₂, ea, eA, ta⟩ := iha formed rfl
      subst ea
      have ta' := facts.retype levels formed ta typeA eA
      obtain ⟨b₁, C, eb, eC, tb⟩ := ihb formed rfl
      subst eb
      have tb' := facts.retype levels formed tb ⟨v, hv, CTyped.instantiate tB ta'⟩
        (eC.trans (CTm.erase_inst0 a₁ B₁).symm)
      exact ⟨.snd (.pair a₁ b₁), b₁, CTm.inst0 a₁ B₁, rfl, rfl, CTm.erase_inst0 a₁ B₁,
        .betaSnd tS hu ta' tb'⟩
  | root step _ _ ihL _ =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨l₁, A₁, el, eA, tl⟩ := ihL formed rfl
      subst el
      obtain ⟨r₁, step₁, er⟩ := facts.lift step
      exact ⟨l₁, r₁, A₁, rfl, er, eA, facts.admitted formed step₁ tl⟩
  | etaPi _ _ _ ihF ihG ihBody =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨f₁, T, ef, eT, tf⟩ := ihF formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eT
      subst ef
      obtain ⟨g₁, T', eg, eT', tg⟩ := ihG formed rfl
      subst eg
      have typePi := CTyped.isType levels tf formed
      obtain ⟨⟨w, hw, tA⟩, typeB⟩ := CIsType.pi_parts typePi
      have tg' := facts.retype levels formed tg typePi eT'
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed ⟨w, hw, tA⟩
      obtain ⟨x, y, B₂, ex, ey, eB, e⟩ := ihBody formed' rfl
      have e' := facts.reequal levels formed' e typeB eB
      obtain ⟨tx, ty⟩ := CEqual.typed levels e' formed'
      have applied : ∀ {h : CTm Head _}, CTyped P Γ' h (.pi A₁ B₁) →
          CTyped P (.snoc Γ' A₁) (.app (h.rename wk) (.var 0)) B₁ := fun th => by
        have := CDerivable.appElim (CTyped.weaken (E := A₁) th) (CDerivable.var (P := P) 0)
        rwa [CTm.inst0_var_rename_liftRen_wk] at this
      have ex' := facts.coherent formed' (applied tf) tx
        (by simp only [CTm.erase, CTm.erase_rename, ex])
      have ey' := facts.coherent formed' (applied tg') ty
        (by simp only [CTm.erase, CTm.erase_rename, ey])
      exact ⟨f₁, g₁, .pi A₁ B₁, rfl, rfl, rfl, .etaPi tf tg' (.trans ex' (.trans e' (.symm ey')))⟩
  | etaSigma _ _ _ _ ihP ihQ ihFst ihSnd =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨p₁, T, ep, eT, tp⟩ := ihP formed rfl
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eT
      subst ep
      obtain ⟨q₁, T', eq, eT', tq⟩ := ihQ formed rfl
      subst eq
      have typeS := CTyped.isType levels tp formed
      obtain ⟨typeA, v, hv, tB⟩ := CIsType.sigma_parts typeS
      have tq' := facts.retype levels formed tq typeS eT'
      obtain ⟨x, y, A₂, ex, ey, eA, e₁⟩ := ihFst formed rfl
      have e₁' := facts.reequal levels formed e₁ typeA eA
      obtain ⟨tx, ty⟩ := CEqual.typed levels e₁' formed
      have efst : CEqual P Γ' (.fst p₁) (.fst q₁) A₁ :=
        .trans (facts.coherent formed (.fstElim tp) tx ex.symm)
          (.trans e₁' (.symm (facts.coherent formed (.fstElim tq') ty ey.symm)))
      obtain ⟨z, z', C, ez, ez', eC, e₂⟩ := ihSnd formed rfl
      have e₂' := facts.reequal levels formed e₂
        ⟨v, hv, CTyped.instantiate tB (.fstElim tp)⟩
        (eC.trans (CTm.erase_inst0 (.fst p₁) B₁).symm)
      obtain ⟨tz, tz'⟩ := CEqual.typed levels e₂' formed
      have tsq : CTyped P Γ' (.snd q₁) (CTm.inst0 (.fst p₁) B₁) :=
        CTyped.convType (.sndElim tq')
          (CIsType.instantiateEq ⟨v, hv, tB⟩ (.fstElim tp) efst).symm
      have esnd : CEqual P Γ' (.snd p₁) (.snd q₁) (CTm.inst0 (.fst p₁) B₁) :=
        .trans (facts.coherent formed (.sndElim tp) tz ez.symm)
          (.trans e₂' (.symm (facts.coherent formed tsq tz' ez'.symm)))
      exact ⟨p₁, q₁, .sigma A₁ B₁, rfl, rfl, rfl, .etaSigma tp tq' efst esnd⟩
  | subEqual _ hu ih =>
      intro Γ' formed eΓ
      obtain ⟨A₁, B₁, U, eA, eB, eU, e⟩ := ih formed eΓ
      obtain rfl := CTm.erase_eq_head eU
      exact ⟨A₁, B₁, eA, eB, .subEqual e hu⟩
  | subUniv c =>
      intro Γ' _ _
      exact ⟨.head _, .head _, rfl, rfl, .subUniv c⟩
  | subPi _ hu _ hu' _ hw _ ihPi ihPi' ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihPi formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_pi eS
      obtain ⟨S', U', eS', eU', tS'⟩ := ihPi' formed rfl
      obtain rfl := CTm.erase_eq_head eU'
      obtain ⟨A₁', B₁', rfl, rfl, rfl⟩ := CTm.erase_eq_pi eS'
      obtain ⟨typeA, typeB⟩ := CIsType.pi_parts ⟨_, hu, tS⟩
      obtain ⟨typeA', typeB'⟩ := CIsType.pi_parts ⟨_, hu', tS'⟩
      obtain ⟨A₂, A₂', W, eA₂, eA₂', eW, e⟩ := ihA formed rfl
      obtain rfl := CTm.erase_eq_head eW
      obtain ⟨tA₂, tA₂'⟩ := CEqual.typed levels e formed
      have eAA' : CTypeEq P Γ' A₁ A₁' :=
        CTypeEq.trans levels (facts.typeEq levels formed typeA ⟨_, hw, tA₂⟩ eA₂.symm)
          (CTypeEq.trans levels ⟨_, hw, e⟩ (facts.typeEq levels formed ⟨_, hw, tA₂'⟩ typeA' eA₂'))
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed typeA
      obtain ⟨B₂, B₂', eB₂, eB₂', le⟩ := ihB formed' rfl
      obtain ⟨typeB₂, typeB₂'⟩ := CBelow.isTypes levels le formed'
      have le' : CBelow P (.snoc Γ' A₁) B₁ B₁' :=
        .subTrans (facts.typeEq levels formed' typeB typeB₂ eB₂.symm).below
          (.subTrans le (facts.typeEq levels formed' typeB₂' (CIsType.ctxConv typeB' eAA'.symm)
            eB₂').below)
      obtain ⟨w₁, hw₁, eAA''⟩ := eAA'
      exact ⟨.pi A₁ B₁, .pi A₁' B₁', rfl, rfl, .subPi tS hu tS' hu' eAA'' hw₁ le'⟩
  | subSigma _ hu _ hu' _ _ ihS ihS' ihA ihB =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨S, U, eS, eU, tS⟩ := ihS formed rfl
      obtain rfl := CTm.erase_eq_head eU
      obtain ⟨A₁, B₁, rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS
      obtain ⟨S', U', eS', eU', tS'⟩ := ihS' formed rfl
      obtain rfl := CTm.erase_eq_head eU'
      obtain ⟨A₁', B₁', rfl, rfl, rfl⟩ := CTm.erase_eq_sigma eS'
      obtain ⟨typeA, typeB⟩ := CIsType.sigma_parts ⟨_, hu, tS⟩
      obtain ⟨typeA', v, hv, tB'⟩ := CIsType.sigma_parts ⟨_, hu', tS'⟩
      obtain ⟨A₂, A₂', eA₂, eA₂', leA⟩ := ihA formed rfl
      obtain ⟨typeA₂, typeA₂'⟩ := CBelow.isTypes levels leA formed
      have leA' : CBelow P Γ' A₁ A₁' :=
        .subTrans (facts.typeEq levels formed typeA typeA₂ eA₂.symm).below
          (.subTrans leA (facts.typeEq levels formed typeA₂' typeA' eA₂').below)
      have formed' : CCtxFormed P (.snoc Γ' A₁) := .snoc formed typeA
      obtain ⟨B₂, B₂', eB₂, eB₂', leB⟩ := ihB formed' rfl
      obtain ⟨typeB₂, typeB₂'⟩ := CBelow.isTypes levels leB formed'
      have leB' : CBelow P (.snoc Γ' A₁) B₁ B₁' :=
        .subTrans (facts.typeEq levels formed' typeB typeB₂ eB₂.symm).below
          (.subTrans leB (facts.typeEq levels formed' typeB₂' ⟨v, hv, CTyped.ctxBelow tB' leA'⟩
            eB₂').below)
      exact ⟨.sigma A₁ B₁, .sigma A₁' B₁', rfl, rfl, .subSigma tS hu tS' hu' leA' leB'⟩
  | subTrans _ _ ih₁ ih₂ =>
      intro Γ' formed eΓ
      subst eΓ
      obtain ⟨A₁, B₁, eA, eB, le₁⟩ := ih₁ formed rfl
      obtain ⟨B₂, C₂, eB₂, eC, le₂⟩ := ih₂ formed rfl
      subst eB
      exact ⟨A₁, C₂, eA, eC, .subTrans le₁ (.subTrans (facts.typeEq levels formed
        (CBelow.isTypes levels le₁ formed).2 (CBelow.isTypes levels le₂ formed).1 eB₂.symm).below
          le₂)⟩

/-- **A formed context is the erasure of a formed annotated context.** -/
theorem lift_ctxFormed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed R Γ) :
    ∃ Γ' : CCtx Head n, CCtxFormed P Γ' ∧ Γ'.erase = Γ := by
  induction formed with
  | nil => exact ⟨.nil, .nil, rfl⟩
  | snoc _ typeA ih =>
      obtain ⟨Γ', formed', rfl⟩ := ih
      obtain ⟨u, hu, tA⟩ := typeA
      obtain ⟨A', U, rfl, eU, tA'⟩ := lifts levels facts tA formed' rfl
      obtain rfl := CTm.erase_eq_head eU
      exact ⟨.snoc Γ' A', .snoc formed' ⟨u, hu, tA'⟩, rfl⟩

/-- **A typing of a formed context lifts** to a typing of a formed annotated context. -/
theorem lift_typed {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (formed : CtxFormed R Γ)
    (typing : Typed R Γ t A) :
    ∃ (Γ' : CCtx Head n) (t' A' : CTm Head n), CCtxFormed P Γ' ∧ Γ'.erase = Γ ∧
      t'.erase = t ∧ A'.erase = A ∧ CTyped P Γ' t' A' := by
  obtain ⟨Γ', formed', eΓ⟩ := lift_ctxFormed levels facts formed
  obtain ⟨t', A', et, eA, typing'⟩ := lifts levels facts typing formed' eΓ
  exact ⟨Γ', t', A', formed', eΓ, et, eA, typing'⟩

/-- **Types lift**: every type of a formed context is the erasure of a type of a formed
annotated context erasing to it. -/
theorem lift_isType {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} (formed : CtxFormed R Γ)
    (type : IsType R Γ A) :
    ∃ (Γ' : CCtx Head n) (A' : CTm Head n), CCtxFormed P Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧
      CIsType P Γ' A' := by
  obtain ⟨Γ', formed', eΓ⟩ := lift_ctxFormed levels facts formed
  obtain ⟨u, hu, tA⟩ := type
  obtain ⟨A', U, eA, eU, tA'⟩ := lifts levels facts tA formed' eΓ
  obtain rfl := CTm.erase_eq_head eU
  exact ⟨Γ', A', formed', eΓ, eA, u, hu, tA'⟩

/-- **Equations of types lift**: two equal types of a formed context are the erasures of two
equal types of one formed annotated context erasing to it. -/
theorem lift_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (formed : CtxFormed R Γ)
    (equal : TypeEq R Γ A B) :
    ∃ (Γ' : CCtx Head n) (A' B' : CTm Head n), CCtxFormed P Γ' ∧ Γ'.erase = Γ ∧
      A'.erase = A ∧ B'.erase = B ∧ CTypeEq P Γ' A' B' := by
  obtain ⟨Γ', formed', eΓ⟩ := lift_ctxFormed levels facts formed
  obtain ⟨u, hu, e⟩ := equal
  obtain ⟨A', B', U, eA, eB, eU, e'⟩ := lifts levels facts e formed' eΓ
  obtain rfl := CTm.erase_eq_head eU
  exact ⟨Γ', A', B', formed', eΓ, eA, eB, u, hu, e'⟩

end Lifting

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
