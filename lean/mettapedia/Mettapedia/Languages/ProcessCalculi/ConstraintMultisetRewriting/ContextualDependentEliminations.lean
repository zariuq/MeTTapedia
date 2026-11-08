import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstantHeadsProjections

/-!
# One reader of elimination spines

An **elimination spine** of a local `h` is `h` followed by applications and projections, in any order:
`fst (g X) A`, `fst (fst (g X))`, `g a b`. Two elimination spines of one local with the same shape of
eliminations are read together along the **literal** Π and Σ types of their prefixes (`elimParts`): an application
step needs both prefix types to be literal Π types and records the argument piece at the two domains; a
projection step needs literal Σ types; the second projection instantiates the family at the first projection of each
prefix. The reader subsumes R97's argument pieces of application spines (`argParts`) and R99's single projection of an
application spine, and reads nested and applied projections.

* **Typing** (`elimParts_typed`): a typed left spine has its literal type as principal type, and every left argument
  has its piece's left type. The reader is symmetric (`elimParts_swap`).
* **Congruence** (`elimParts_congr`): when the pieces hold, the spines are equal at the left literal type.
* **Injectivity** (`elimParts_holds`): an algorithmic comparison of the two spines as spines makes every piece hold,
  and its type is the literal type up to equality.
* **Exactness at a base type** (`elim_exact`): two typed elimination spines of one local are equal at a base type
  exactly when the pieces hold.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEliminations

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentDecisiveFragment
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentRank
open ContextualDependentSpinesMany ContextualDependentConversionBudget ContextualDependentFragmentDecisive
open ContextualDependentRigidDecomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The reader -/

section Reading

variable {n : Nat}

/-- What the reader returns: the argument pieces, outermost last, and the literal types of the two spines. -/
abbrev Read (Head : Type) (n : Nat) := List (Piece Head n) × Tm Head n × Tm Head n

/-- An application step: both prefix types are literal Π types. -/
def appStep (a b : Tm Head n) : Option (Read Head n) → Option (Read Head n)
  | some (pieces, .pi DL EL, .pi DR ER) => some (pieces ++ [⟨DL, a, DR, b⟩], inst0 a EL, inst0 b ER)
  | _ => none

/-- A first projection step: both prefix types are literal Σ types. -/
def fstStep : Option (Read Head n) → Option (Read Head n)
  | some (pieces, .sigma AL _, .sigma AR _) => some (pieces, AL, AR)
  | _ => none

/-- A second projection step: the families are instantiated at the first projection of each prefix. -/
def sndStep (p q : Tm Head n) : Option (Read Head n) → Option (Read Head n)
  | some (pieces, .sigma _ BL, .sigma _ BR) => some (pieces, inst0 (.fst p) BL, inst0 (.fst q) BR)
  | _ => none

/-- **The argument pieces of two elimination spines of one local**, along the literal Π and Σ types of their
prefixes. -/
def elimParts (Γ : Ctx Head n) : Tm Head n → Tm Head n → Option (Read Head n)
  | .var h, .var h' => if h = h' then some ([], Ctx.lookup Γ h, Ctx.lookup Γ h) else none
  | .app f a, .app g b => appStep a b (elimParts Γ f g)
  | .fst p, .fst q => fstStep (elimParts Γ p q)
  | .snd p, .snd q => sndStep p q (elimParts Γ p q)
  | _, _ => none

theorem appStep_some {a b : Tm Head n} {read : Option (Read Head n)} {result : Read Head n}
    (found : appStep a b read = some result) :
    ∃ pieces DL EL DR ER, read = some (pieces, .pi DL EL, .pi DR ER) ∧
      result = (pieces ++ [⟨DL, a, DR, b⟩], inst0 a EL, inst0 b ER) := by
  unfold appStep at found
  split at found
  · cases found
    exact ⟨_, _, _, _, _, rfl, rfl⟩
  · cases found

theorem fstStep_some {read : Option (Read Head n)} {result : Read Head n} (found : fstStep read = some result) :
    ∃ pieces AL BL AR BR, read = some (pieces, .sigma AL BL, .sigma AR BR) ∧ result = (pieces, AL, AR) := by
  unfold fstStep at found
  split at found
  · cases found
    exact ⟨_, _, _, _, _, rfl, rfl⟩
  · cases found

theorem sndStep_some {p q : Tm Head n} {read : Option (Read Head n)} {result : Read Head n}
    (found : sndStep p q read = some result) :
    ∃ pieces AL BL AR BR, read = some (pieces, .sigma AL BL, .sigma AR BR) ∧
      result = (pieces, inst0 (.fst p) BL, inst0 (.fst q) BR) := by
  unfold sndStep at found
  split at found
  · cases found
    exact ⟨_, _, _, _, _, rfl, rfl⟩
  · cases found

/-- A piece read in the other orientation. -/
def Piece.swap (piece : Piece Head n) : Piece Head n :=
  ⟨piece.rightType, piece.right, piece.leftType, piece.left⟩

/-- **The reader is symmetric.** -/
theorem elimParts_swap (Γ : Ctx Head n) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) → elimParts Γ right left = some (pieces.map Piece.swap, TR, TL)
  | .var h, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i h'
      simp only [elimParts] at found
      split at found
      · rename_i same
        subst same
        cases found
        simp [elimParts]
      · cases found
  | .app f a, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      change appStep b a (elimParts Γ g f) = _
      rw [elimParts_swap Γ f g read]
      simp [appStep, Piece.swap]
  | .fst p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      change fstStep (elimParts Γ q p) = _
      rw [elimParts_swap Γ p q read]
      rfl
  | .snd p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      change sndStep q p (elimParts Γ q p) = _
      rw [elimParts_swap Γ p q read]
      rfl
  | .const _, _, _, _, _, found => by cases found
  | .head _, _, _, _, _, found => by cases found
  | .pi _ _, _, _, _, _, found => by cases found
  | .sigma _ _, _, _, _, _, found => by cases found
  | .id _ _ _, _, _, _, _, found => by cases found
  | .lam _, _, _, _, _, found => by cases found
  | .pair _ _, _, _, _, _, found => by cases found
  | .refl _, _, _, _, _, found => by cases found

/-- Both read spines are neutral. -/
theorem elimParts_neutral {roles : Roles Head} (Γ : Ctx Head n) :
    ∀ (left right : Tm Head n) {read : Read Head n},
      elimParts Γ left right = some read → Neutral roles left ∧ Neutral roles right
  | .var h, right, read, found => by
      cases right
      all_goals first | cases found | skip
      exact ⟨.var _, .var _⟩
  | .app f a, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := appStep_some found
      obtain ⟨nf, ng⟩ := elimParts_neutral Γ f g prefixRead
      exact ⟨.app nf, .app ng⟩
  | .fst p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := fstStep_some found
      obtain ⟨np, nq⟩ := elimParts_neutral Γ p q prefixRead
      exact ⟨.fst np, .fst nq⟩
  | .snd p, right, read, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨_, _, _, _, _, prefixRead, _⟩ := sndStep_some found
      obtain ⟨np, nq⟩ := elimParts_neutral Γ p q prefixRead
      exact ⟨.snd np, .snd nq⟩
  | .const _, _, _, found => by cases found
  | .head _, _, _, found => by cases found
  | .pi _ _, _, _, found => by cases found
  | .sigma _ _, _, _, found => by cases found
  | .id _ _ _, _, _, found => by cases found
  | .lam _, _, _, found => by cases found
  | .pair _ _, _, _, found => by cases found
  | .refl _, _, _, found => by cases found

end Reading

/-! ## Typing, congruence and injectivity -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include facts in
/-- **A typed elimination spine has its literal type as principal type**, and every left argument has the left type
of its piece. -/
theorem elimParts_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR C : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) → TypedEquality.Typed S.R Γ left C →
      TypedEquality.Typed S.R Γ left TL ∧ (∀ U, TypedEquality.Typed S.R Γ left U → TypeLe S.R Γ TL U) ∧
        ∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType
  | .var h, right, pieces, TL, TR, C, found, _ => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · cases found
        exact ⟨.var h, fun U typedU => Typed.generation typedU, fun _ member => by simp at member⟩
      · cases found
  | .app f a, right, pieces, TL, TR, C, found, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      obtain ⟨A, B, tf, ta, _⟩ := Typed.generation typed
      obtain ⟨tfL, principal, prefixTyped⟩ := elimParts_typed formed f g read tf
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (principal _ tf) (Typed.isType tf formed) formed
      have ta' : TypedEquality.Typed S.R Γ a DL := Typed.convType ta domains.symm
      refine ⟨Derivable.appElim tfL ta', ?_, ?_⟩
      · intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (principal _ tf'') (Typed.isType tf'' formed) formed
        have instantiated : Below S.R Γ (inst0 a EL) (inst0 a B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        exact .sub instantiated le'
      · intro piece member
        rcases List.mem_append.mp member with inPrefix | isLast
        · exact prefixTyped piece inPrefix
        · rw [List.mem_singleton.mp isLast]
          exact ta'
  | .fst p, right, pieces, TL, TR, C, found, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      obtain ⟨A, B, tp, _⟩ := Typed.generation typed
      obtain ⟨tpL, principal, prefixTyped⟩ := elimParts_typed formed p q read tp
      refine ⟨Derivable.fstElim tpL, ?_, prefixTyped⟩
      intro U typedU
      obtain ⟨A', B', tp', le'⟩ := Typed.generation typedU
      obtain ⟨leA, _⟩ := TypeLe.sigma_parts facts (principal _ tp') (Typed.isType tp' formed) formed
      exact .sub leA le'
  | .snd p, right, pieces, TL, TR, C, found, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      obtain ⟨A, B, tp, _⟩ := Typed.generation typed
      obtain ⟨tpL, principal, prefixTyped⟩ := elimParts_typed formed p q read tp
      refine ⟨Derivable.sndElim tpL, ?_, prefixTyped⟩
      intro U typedU
      obtain ⟨A', B', tp', le'⟩ := Typed.generation typedU
      obtain ⟨_, leB⟩ := TypeLe.sigma_parts facts (principal _ tp') (Typed.isType tp' formed) formed
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpL
      have stepB : Below S.R Γ (inst0 (.fst p) BL) (inst0 (.fst p) B') :=
        Derivable.substitutes leB (SubstMor.single tFst)
      exact .sub stepB le'
  | .const _, _, _, _, _, _, found, _ => by cases found
  | .head _, _, _, _, _, _, found, _ => by cases found
  | .pi _ _, _, _, _, _, _, found, _ => by cases found
  | .sigma _ _, _, _, _, _, _, found, _ => by cases found
  | .id _ _ _, _, _, _, _, _, found, _ => by cases found
  | .lam _, _, _, _, _, _, found, _ => by cases found
  | .pair _ _, _, _, _, _, _, found, _ => by cases found
  | .refl _, _, _, _, _, _, found, _ => by cases found

/-- **Congruence**: when the pieces hold, the two spines are equal at the left literal type. -/
theorem elimParts_congr {n : Nat} {Γ : Ctx Head n} :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) → (∀ piece ∈ pieces, piece.Holds S.R Γ) →
      Equal S.R Γ left right TL
  | .var h, right, pieces, TL, TR, found, _ => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · rename_i same
        subst same
        cases found
        exact .refl (.var h)
      · cases found
  | .app f a, right, pieces, TL, TR, found, held => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      have inner := elimParts_congr f g read
        (fun piece member => held piece (List.mem_append_left _ member))
      exact Derivable.appCong inner (held _ (List.mem_append_right _ List.mem_cons_self)).2
  | .fst p, right, pieces, TL, TR, found, held => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      exact .fstCong (elimParts_congr p q read held)
  | .snd p, right, pieces, TL, TR, found, held => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      exact .sndCong (elimParts_congr p q read held)
  | .const _, _, _, _, _, found, _ => by cases found
  | .head _, _, _, _, _, found, _ => by cases found
  | .pi _ _, _, _, _, _, found, _ => by cases found
  | .sigma _ _, _, _, _, _, found, _ => by cases found
  | .id _ _ _, _, _, _, _, found, _ => by cases found
  | .lam _, _, _, _, _, found, _ => by cases found
  | .pair _ _, _, _, _, _, found, _ => by cases found
  | .refl _, _, _, _, _, found, _ => by cases found

include facts roots heads algebra in
/-- **Injectivity of elimination spines**: an algorithmic comparison of the two spines as spines makes every piece
hold; the compared type is the left literal type up to equality, and the two literal types are equal. -/
theorem elimParts_holds {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR U : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) →
      Algorithmic S.R S.roles (.spines Γ left right U) →
      TypedEquality.Typed S.R Γ left TL → TypedEquality.Typed S.R Γ right TR →
      (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      TypeEq S.R Γ TL U ∧ TypeEq S.R Γ TL TR ∧ ∀ piece ∈ pieces, piece.Holds S.R Γ
  | .var h, right, pieces, TL, TR, U, found, derivation, tl, _, _ => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · rename_i same
        subst same
        cases found
        cases derivation
        have isT := Typed.isType tl formed
        exact ⟨isT.refl, isT.refl, fun _ member => by simp at member⟩
      · cases found
  | .app f a, right, pieces, TL, TR, U, found, derivation, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      cases derivation with
      | app inner terms =>
          cases inner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tf, _, _⟩ := Typed.generation tl
              obtain ⟨tfL, _, _⟩ := elimParts_typed facts formed f g read tf
              obtain ⟨A₂, B₂, tg, _, _⟩ := Typed.generation tr
              obtain ⟨tgR, _, _⟩ := elimParts_typed facts formed g f (elimParts_swap Γ f g read) tg
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := elimParts_holds formed f g read prefixSpines tfL tgR
                (fun piece member => typed piece (List.mem_append_left _ member))
              obtain ⟨domains, codomains⟩ :=
                (ContextualDependentRigid.typeEq_pi_iff facts formed).mp (TypeEq.trans S.levels atU red.typeEq)
              obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp prefixTypes
              obtain ⟨ta, _⟩ := typed _ (List.mem_append_right _ List.mem_cons_self)
              have firsts : Equal S.R Γ a b DL :=
                .subEq (Algorithmic.sound_terms facts roots heads algebra formed terms) domains.symm.below
              obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (Typed.isType tgR formed)
              have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
              refine ⟨TypeEq.instantiate codomains ta,
                TypeEq.trans S.levels (TypeEq.instantiate codomainsLR ta) (TypeEq.of_instantiateEq tER' hv' ta firsts),
                ?_⟩
              intro piece member
              rcases List.mem_append.mp member with inPrefix | isLast
              · exact prefixHolds piece inPrefix
              · rw [List.mem_singleton.mp isLast]
                exact ⟨domainsLR, firsts⟩
  | .fst p, right, pieces, TL, TR, U, found, derivation, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      cases derivation with
      | fst inner =>
          cases inner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
              obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
              obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
              obtain ⟨tqR, _, _⟩ := elimParts_typed facts formed q p (elimParts_swap Γ p q read) tq
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := elimParts_holds formed p q read prefixSpines tpL tqR typed
              obtain ⟨domains, _⟩ :=
                (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp (TypeEq.trans S.levels atU red.typeEq)
              obtain ⟨domainsLR, _⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp prefixTypes
              exact ⟨domains, domainsLR, prefixHolds⟩
  | .snd p, right, pieces, TL, TR, U, found, derivation, tl, tr, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      cases derivation with
      | snd inner =>
          cases inner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
              obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
              obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
              obtain ⟨tqR, _, _⟩ := elimParts_typed facts formed q p (elimParts_swap Γ p q read) tq
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := elimParts_holds formed p q read prefixSpines tpL tqR typed
              obtain ⟨_, codomains⟩ :=
                (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp (TypeEq.trans S.levels atU red.typeEq)
              obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp prefixTypes
              have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpL
              have firsts : Equal S.R Γ (.fst p) (.fst q) AL := .fstCong (elimParts_congr p q read prefixHolds)
              obtain ⟨_, ⟨v', hv', tBR⟩⟩ := IsType.sigma_parts (Typed.isType tqR formed)
              have tBR' := Typed.stable tBR (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
              exact ⟨TypeEq.instantiate codomains tFst,
                TypeEq.trans S.levels (TypeEq.instantiate codomainsLR tFst)
                  (TypeEq.of_instantiateEq tBR' hv' tFst firsts), prefixHolds⟩
  | .const _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .head _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .pi _ _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .sigma _ _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .id _ _ _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .lam _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .pair _ _, _, _, _, _, _, found, _, _, _, _ => by cases found
  | .refl _, _, _, _, _, _, found, _, _, _, _ => by cases found

include facts roots heads algebra complete in
/-- **Elimination spines of one local decompose exactly at a base type**: two typed spines read together are equal
exactly when every piece holds. This covers application spines, single, nested and applied projections. -/
theorem elim_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {left right : Tm Head n}
    {pieces : List (Piece Head n)} {TL TR C : Tm Head n} (found : elimParts Γ left right = some (pieces, TL, TR))
    (base : BaseType S C) (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨tlL, principalL, leftTyped⟩ := elimParts_typed facts formed left right found tl
  obtain ⟨trR, _, rightTyped⟩ := elimParts_typed facts formed right left (elimParts_swap Γ left right found) tr
  have typed : ∀ piece ∈ pieces, piece.Typed S.R Γ := fun piece member =>
    ⟨leftTyped piece member, rightTyped _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩
  constructor
  · intro same
    obtain ⟨leftNeutral, rightNeutral⟩ := elimParts_neutral (roles := S.roles) Γ left right found
    obtain ⟨U, spines⟩ := terms_neutral_spines base leftNeutral rightNeutral (complete formed same)
    exact (elimParts_holds facts roots heads algebra formed left right found spines tlL trR typed).2.2
  · intro held
    exact .subEq (elimParts_congr left right found held) (TypeLe.toBelow (principalL C tl) (Typed.isType tl formed))

/-! ## Normal forms and weights -/

theorem ArgWeights.snoc {n : Nat} {Γ : Ctx Head n} :
    ∀ {as ds : List (Tm Head n)} {ws : List Nat} {a D : Tm Head n} {w : Nat},
      ArgWeights S Γ as ds ws → HasWeight S Γ a D w → ArgWeights S Γ (as ++ [a]) (ds ++ [D]) (ws ++ [w])
  | [], [], [], _, _, _, .nil, weighs => .cons weighs .nil
  | _ :: _, _ :: _, _ :: _, _, _, _, .cons first rest, weighs => .cons first (ArgWeights.snoc rest weighs)

variable (rigid : ∀ name, S.roles name = .rigid)

include facts roots heads algebra rigid complete in
/-- **The normal form of an elimination spine** is an elimination spine of the normal forms of its arguments, and
weighs at least one more than they do. -/
theorem elimParts_normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) → TypedEquality.Typed S.R Γ left TL →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) →
      ∃ (normal : Tm Head n) (ws : List Nat),
        ArgWeights S Γ (pieces.map (·.left)) (pieces.map (·.leftType)) ws ∧
        Long S.R S.roles (.spine Γ normal TL) ∧ Equal S.R Γ left normal TL ∧ ws.sum + 1 ≤ weight normal
  | .var h, right, pieces, TL, TR, found, tl, _ => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · cases found
        have isT := Typed.isType tl formed
        exact ⟨.var h, [], .nil, .var h isT.refl, .refl tl, by simp [weight]⟩
      · cases found
  | .app f a, right, pieces, TL, TR, found, tl, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation tl
      obtain ⟨tfL, _, _⟩ := elimParts_typed facts formed f g read tf
      obtain ⟨fn, ws, weights, longF, equalF, weighed⟩ := elimParts_normal formed f g read tfL
        (fun piece member => typed piece (List.mem_append_left _ member))
      have ta := typed _ (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      have tPi := Typed.isType tfL formed
      obtain ⟨_, ⟨v, hv, tE⟩⟩ := IsType.pi_parts tPi
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (inst0 a EL)) :=
        .app longF (IsType.refl tPi) nA.1 (TypeEq.of_instantiateEq tE hv ta nA.2)
      refine ⟨.app fn na, ws ++ [weight na], ?_, longApp, Derivable.appCong equalF nA.2, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact ArgWeights.snoc weights ⟨na, nA, rfl⟩
      · simp only [weight, List.sum_append, List.sum_cons, List.sum_nil]
        omega
  | .fst p, right, pieces, TL, TR, found, tl, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
      obtain ⟨pn, ws, weights, longP, equalP, weighed⟩ := elimParts_normal formed p q read tpL typed
      have tSigma := Typed.isType tpL formed
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.sigma_parts tSigma
      refine ⟨.fst pn, ws, weights, .fst longP (IsType.refl tSigma) (IsType.refl ⟨u, hu, tA⟩), .fstCong equalP, ?_⟩
      simp only [weight]
      omega
  | .snd p, right, pieces, TL, TR, found, tl, typed => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := elimParts_typed facts formed p q read tp
      obtain ⟨pn, ws, weights, longP, equalP, weighed⟩ := elimParts_normal formed p q read tpL typed
      have tSigma := Typed.isType tpL formed
      obtain ⟨_, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts tSigma
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpL
      have firsts : Equal S.R Γ (.fst p) (.fst pn) AL := .fstCong equalP
      refine ⟨.snd pn, ws, weights, .snd longP (IsType.refl tSigma) (TypeEq.of_instantiateEq tB hv tFst firsts),
        .sndCong equalP, ?_⟩
      simp only [weight]
      omega
  | .const _, _, _, _, _, found, _, _ => by cases found
  | .head _, _, _, _, _, found, _, _ => by cases found
  | .pi _ _, _, _, _, _, found, _, _ => by cases found
  | .sigma _ _, _, _, _, _, found, _, _ => by cases found
  | .id _ _ _, _, _, _, _, found, _, _ => by cases found
  | .lam _, _, _, _, _, found, _, _ => by cases found
  | .pair _ _, _, _, _, _, found, _, _ => by cases found
  | .refl _, _, _, _, _, found, _, _ => by cases found

include facts roots heads algebra rigid complete in
/-- **Elimination spines weigh more than their pieces** at a base type: the decomposition lowers the normal weight
by at least two. -/
theorem elim_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {left right : Tm Head n}
    {pieces : List (Piece Head n)} {TL TR C : Tm Head n} (found : elimParts Γ left right = some (pieces, TL, TR))
    (base : BaseType S C) (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  have swapped := elimParts_swap Γ left right found
  obtain ⟨tlL, principalL, leftTyped⟩ := elimParts_typed facts formed left right found tl
  obtain ⟨trR, principalR, rightTyped⟩ := elimParts_typed facts formed right left swapped tr
  obtain ⟨ln, ws, weights, longL, equalL, weighL⟩ :=
    elimParts_normal facts roots heads algebra complete rigid formed left right found tlL leftTyped
  obtain ⟨rn, ws', weights', longR, equalR, weighR⟩ :=
    elimParts_normal facts roots heads algebra complete rigid formed right left swapped trR rightTyped
  have baseC := ContextualDependentSpinesMany.BaseType.base facts formed base
  have isC := Typed.isType tl formed
  have belowL := TypeLe.toBelow (principalL C tl) isC
  have belowR := TypeLe.toBelow (principalR C tr) isC
  have equalL' : Equal S.R Γ left ln C := .subEq equalL belowL
  have equalR' : Equal S.R Γ right rn C := .subEq equalR belowR
  have normalL : NormalForm S.R S.roles Γ left ln C :=
    ⟨.neutral longL belowL (Equal.typed equalL' formed).2 baseC, equalL'⟩
  have normalR : NormalForm S.R S.roles Γ right rn C :=
    ⟨.neutral longR belowR (Equal.typed equalR' formed).2 baseC, equalR'⟩
  have rightWeights : ArgWeights S Γ (pieces.map (·.right)) (pieces.map (·.rightType)) ws' := by
    simpa [List.map_map, Function.comp_def, Piece.swap] using weights'
  refine ⟨ws.sum + ws'.sum, weight ln, weight rn, ArgWeights.piecesOf (S := S) weights rightWeights,
    ⟨ln, normalL, rfl⟩, ⟨rn, normalR, rfl⟩, by omega⟩

include facts in
/-- **The pieces are typed** on both sides. -/
theorem elimParts_pieces_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {left right : Tm Head n}
    {pieces : List (Piece Head n)} {TL TR C D : Tm Head n} (found : elimParts Γ left right = some (pieces, TL, TR))
    (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right D) :
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨_, _, leftTyped⟩ := elimParts_typed facts formed left right found tl
  obtain ⟨_, _, rightTyped⟩ := elimParts_typed facts formed right left (elimParts_swap Γ left right found) tr
  exact fun piece member => ⟨leftTyped piece member, rightTyped _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩

end Theory

end ContextualDependentEliminations
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
