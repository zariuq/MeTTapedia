import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthAnyBase

/-!
# One reading of elimination spines, along reducts, exact at every type

**The reading** (`ElimRel`). Two elimination spines of one head, applications and projections in any order and of
the same shape on both sides, are read together along the types of their prefixes: an application step needs both
prefix types to **reduce** to Π types and records the argument piece at the two domains; a projection step needs
both to reduce to Σ types; the second projection instantiates the family at the first projection of each prefix.

It is one relation for the earlier readings:

* R97/R121's argument pieces of application spines along reducts (`ArgRel`): `ElimRel.of_argRel`;
* R124's equal projection of two application spines (`SpineRel.proj`): `ElimRel.of_projection`;
* R107's reader of elimination spines along **literal** types (`elimParts`): `ElimRel.of_elimParts`.

**Its theory.**

* It is kept by every substitution and every renaming (`ElimRel.subst`, `ElimRel.rename`): a type that reduces to a
  Π or Σ type still does after a substitution. The literal reader has no such closure for the types it does not
  read, and a normalizing reader does not commute with substitution.
* It is symmetric (`ElimRel.swap`), and both spines of a neutral head are neutral (`ElimRel.neutral`).
* **Typing** (`ElimRel.typed_left`, `ElimRel.pieces_typed`): a typed spine has the type read as principal type, and
  every argument has its piece's type.
* **Congruence** (`ElimRel.congr`): when the pieces hold, the spines are equal at the left type read.
* **Injectivity** (`ElimRel.holds`): an algorithmic comparison of the two spines as spines makes every piece hold.
* **Exactness at every type** (`ElimRel.exact`): two typed elimination spines of one variable are equal at a type,
  whatever the type, exactly when the pieces hold. R124's `argRel_exact_any` and `projRel_exact_any` are the cases
  of applications only and of one projection above them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentRigidDecomposition
open ContextualDependentSpinesMany ContextualDependentDecisiveFragment
open ContextualDependentSpineEta (descends piece_reflects renamePiece)
open ContextualDependentEliminations (Piece.swap elimParts appStep_some fstStep_some sndStep_some)
open ContextualDependentConstantHeadsProjections (project)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The reading -/

/-- **Two elimination spines of one head, read along types that reduce to Π and Σ types**: the argument pieces,
innermost first, and the types read of the two spines. `type` is the type at which the head is read. -/
inductive ElimRel (R : Rules Head) {n : Nat} (head type : Tm Head n) :
    Tm Head n → Tm Head n → List (Piece Head n) → Tm Head n → Tm Head n → Prop
  | nil : ElimRel R head type head head [] type type
  | app {f g a b TL TR DL DR : Tm Head n} {EL ER : Tm Head (n + 1)} {pieces : List (Piece Head n)} :
      ElimRel R head type f g pieces TL TR → Reduces R TL (.pi DL EL) → Reduces R TR (.pi DR ER) →
      ElimRel R head type (.app f a) (.app g b) (pieces ++ [⟨DL, a, DR, b⟩]) (inst0 a EL) (inst0 b ER)
  | fst {p q TL TR AL AR : Tm Head n} {BL BR : Tm Head (n + 1)} {pieces : List (Piece Head n)} :
      ElimRel R head type p q pieces TL TR → Reduces R TL (.sigma AL BL) → Reduces R TR (.sigma AR BR) →
      ElimRel R head type (.fst p) (.fst q) pieces AL AR
  | snd {p q TL TR AL AR : Tm Head n} {BL BR : Tm Head (n + 1)} {pieces : List (Piece Head n)} :
      ElimRel R head type p q pieces TL TR → Reduces R TL (.sigma AL BL) → Reduces R TR (.sigma AR BR) →
      ElimRel R head type (.snd p) (.snd q) pieces (inst0 (.fst p) BL) (inst0 (.fst q) BR)

namespace ElimRel

variable {R : Rules Head}

/-- **The reading is symmetric.** -/
theorem swap {n : Nat} {head type left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel R head type left right pieces TL TR) :
    ElimRel R head type right left (pieces.map Piece.swap) TR TL := by
  induction read with
  | nil => exact .nil
  | app _ left right ih =>
      rw [List.map_append]
      exact .app ih right left
  | fst _ left right ih => exact .fst ih right left
  | snd _ left right ih => exact .snd ih right left

/-- **The reading is kept by every substitution.** -/
theorem subst {n m : Nat} (σ : Sub Head n m) {head type left right TL TR : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimRel R head type left right pieces TL TR) :
    ElimRel R (Presentation.subst σ head) (Presentation.subst σ type) (Presentation.subst σ left)
      (Presentation.subst σ right) (pieces.map (Piece.subst σ)) (Presentation.subst σ TL)
      (Presentation.subst σ TR) := by
  induction read with
  | nil => exact .nil
  | app _ left right ih =>
      rw [List.map_append, subst_inst0, subst_inst0]
      exact .app ih (Reduces.substitute left σ) (Reduces.substitute right σ)
  | fst _ left right ih => exact .fst ih (Reduces.substitute left σ) (Reduces.substitute right σ)
  | snd _ left right ih =>
      rw [subst_inst0, subst_inst0]
      exact .snd ih (Reduces.substitute left σ) (Reduces.substitute right σ)

/-- **The reading is kept by every renaming.** -/
theorem rename {n m : Nat} (ρ : Ren n m) {head type left right TL TR : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimRel R head type left right pieces TL TR) :
    ElimRel R (Presentation.rename ρ head) (Presentation.rename ρ type) (Presentation.rename ρ left)
      (Presentation.rename ρ right) (pieces.map (renamePiece ρ)) (Presentation.rename ρ TL)
      (Presentation.rename ρ TR) := by
  induction read with
  | nil => exact .nil
  | app _ left right ih =>
      rw [List.map_append, rename_inst0, rename_inst0]
      exact .app ih (Reduces.rename' left ρ) (Reduces.rename' right ρ)
  | fst _ left right ih => exact .fst ih (Reduces.rename' left ρ) (Reduces.rename' right ρ)
  | snd _ left right ih =>
      rw [rename_inst0, rename_inst0]
      exact .snd ih (Reduces.rename' left ρ) (Reduces.rename' right ρ)

/-- Both spines of a neutral head are neutral. -/
theorem neutral {roles : Roles Head} {n : Nat} {head type left right TL TR : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimRel R head type left right pieces TL TR)
    (isNeutral : Neutral roles head) : Neutral roles left ∧ Neutral roles right := by
  induction read with
  | nil => exact ⟨isNeutral, isNeutral⟩
  | app _ _ _ ih => exact ⟨.app ih.1, .app ih.2⟩
  | fst _ _ _ ih => exact ⟨.fst ih.1, .fst ih.2⟩
  | snd _ _ _ ih => exact ⟨.snd ih.1, .snd ih.2⟩

end ElimRel

/-! ## Typing, congruence and injectivity -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **A typed elimination spine has the type read as principal type**, and every left argument has the left type of
its piece, when the head has its type as principal type. -/
theorem ElimRel.typed_left {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {head type : Tm Head n}
    (th : TypedEquality.Typed S.R Γ head type)
    (principal : ∀ U, TypedEquality.Typed S.R Γ head U → TypeLe S.R Γ type U)
    {left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R head type left right pieces TL TR) :
    ∀ {C : Tm Head n}, TypedEquality.Typed S.R Γ left C →
      TypedEquality.Typed S.R Γ left TL ∧ (∀ U, TypedEquality.Typed S.R Γ left U → TypeLe S.R Γ TL U) ∧
        ∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType := by
  induction read with
  | nil => exact fun _ => ⟨th, principal, fun _ member => by simp at member⟩
  | @app f g a b TL TR DL DR EL ER pieces inner redL redR ih =>
      intro C typed
      obtain ⟨A, B, tf, ta, _⟩ := Typed.generation typed
      obtain ⟨tfL, principalF, prefixTyped⟩ := ih tf
      have toPi : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tfL formed)
      have lePi : ∀ {U}, TypeLe S.R Γ TL U → TypeLe S.R Γ (.pi DL EL) U := fun le => by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toPi
        exact .conv e hu le
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (lePi (principalF _ tf)) (Typed.isType tf formed) formed
      have ta' : TypedEquality.Typed S.R Γ a DL := Typed.convType ta domains.symm
      refine ⟨Derivable.appElim (Typed.convType tfL toPi) ta', ?_, ?_⟩
      · intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (lePi (principalF _ tf'')) (Typed.isType tf'' formed) formed
        have instantiated : Below S.R Γ (inst0 a EL) (inst0 a B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        exact .sub instantiated le'
      · intro piece member
        rcases List.mem_append.mp member with inPrefix | isLast
        · exact prefixTyped piece inPrefix
        · rw [List.mem_singleton.mp isLast]
          exact ta'
  | @fst p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro C typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation typed
      obtain ⟨tpL, principalP, prefixTyped⟩ := ih tp
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      have leSigma : ∀ {U}, TypeLe S.R Γ TL U → TypeLe S.R Γ (.sigma AL BL) U := fun le => by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toSigma
        exact .conv e hu le
      refine ⟨Derivable.fstElim (Typed.convType tpL toSigma), ?_, prefixTyped⟩
      intro U typedU
      obtain ⟨A', B', tp', le'⟩ := Typed.generation typedU
      obtain ⟨leA, _⟩ := TypeLe.sigma_parts facts (leSigma (principalP _ tp')) (Typed.isType tp' formed) formed
      exact .sub leA le'
  | @snd p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro C typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation typed
      obtain ⟨tpL, principalP, prefixTyped⟩ := ih tp
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      have leSigma : ∀ {U}, TypeLe S.R Γ TL U → TypeLe S.R Γ (.sigma AL BL) U := fun le => by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toSigma
        exact .conv e hu le
      have tpSigma := Typed.convType tpL toSigma
      refine ⟨Derivable.sndElim tpSigma, ?_, prefixTyped⟩
      intro U typedU
      obtain ⟨A', B', tp', le'⟩ := Typed.generation typedU
      obtain ⟨_, leB⟩ := TypeLe.sigma_parts facts (leSigma (principalP _ tp')) (Typed.isType tp' formed) formed
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpSigma
      have stepB : Below S.R Γ (inst0 (.fst p) BL) (inst0 (.fst p) B') :=
        Derivable.substitutes leB (SubstMor.single tFst)
      exact .sub stepB le'

include facts roots heads in
/-- **Both spines' arguments are typed at their own domains.** -/
theorem ElimRel.pieces_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {head type : Tm Head n}
    (th : TypedEquality.Typed S.R Γ head type)
    (principal : ∀ U, TypedEquality.Typed S.R Γ head U → TypeLe S.R Γ type U)
    {left right TL TR C C' : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R head type left right pieces TL TR)
    (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C') :
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨_, _, leftTyped⟩ := read.typed_left facts roots heads formed th principal tl
  obtain ⟨_, _, rightTyped⟩ := read.swap.typed_left facts roots heads formed th principal tr
  exact fun piece member => ⟨leftTyped piece member, rightTyped _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩

include facts roots heads in
/-- **Congruence**: when the pieces hold, the two spines are equal at the left type read. -/
theorem ElimRel.congr {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {head type : Tm Head n}
    (th : TypedEquality.Typed S.R Γ head type) {left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R head type left right pieces TL TR) :
    (∀ piece ∈ pieces, piece.Holds S.R Γ) → Equal S.R Γ left right TL := by
  induction read with
  | nil => exact fun _ => .refl th
  | @app f g a b TL TR DL DR EL ER pieces inner redL redR ih =>
      intro held
      have below := ih fun piece member => held piece (List.mem_append_left _ member)
      have toPi : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType (Equal.typed below formed).1 formed)
      exact Derivable.appCong (Equal.convType below toPi)
        (held _ (List.mem_append_right _ List.mem_cons_self)).2
  | @fst p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro held
      have below := ih held
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType (Equal.typed below formed).1 formed)
      exact .fstCong (Equal.convType below toSigma)
  | @snd p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro held
      have below := ih held
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType (Equal.typed below formed).1 formed)
      exact .sndCong (Equal.convType below toSigma)

include facts roots heads algebra in
/-- **Injectivity of elimination spines of a variable**: an algorithmic comparison of the two spines as spines makes
every piece hold; the compared type is the left type read up to equality, and the two types read are equal. -/
theorem ElimRel.holds {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n}
    {left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR) :
    ∀ {U : Tm Head n}, Algorithmic S.R S.roles (.spines Γ left right U) →
      TypedEquality.Typed S.R Γ left TL → TypedEquality.Typed S.R Γ right TR →
      (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      TypeEq S.R Γ TL U ∧ TypeEq S.R Γ TL TR ∧ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
    fun U typed => Typed.generation typed
  induction read with
  | nil =>
      intro U derivation tl _ _
      cases derivation
      have isT := Typed.isType tl formed
      exact ⟨isT.refl, isT.refl, fun _ member => by simp at member⟩
  | @app f g a b TL TR DL DR EL ER pieces inner redL redR ih =>
      intro U derivation tl tr typed
      cases derivation with
      | app spinesInner terms =>
          cases spinesInner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tf, _, _⟩ := Typed.generation tl
              obtain ⟨tfL, _, _⟩ := inner.typed_left facts roots heads formed th principal tf
              obtain ⟨A₂, B₂, tg, _, _⟩ := Typed.generation tr
              obtain ⟨tgR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tg
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := ih prefixSpines tfL tgR
                (fun piece member => typed piece (List.mem_append_left _ member))
              have toPiL : TypeEq S.R Γ TL (.pi DL EL) :=
                Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tfL formed)
              have toPiR : TypeEq S.R Γ TR (.pi DR ER) :=
                Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tgR formed)
              obtain ⟨domains, codomains⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels atU red.typeEq))
              obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels prefixTypes toPiR))
              obtain ⟨ta, _⟩ := typed _ (List.mem_append_right _ List.mem_cons_self)
              have firsts : Equal S.R Γ a b DL :=
                .subEq (Algorithmic.sound_terms facts roots heads algebra formed terms) domains.symm.below
              obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiR)
              have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
              refine ⟨TypeEq.instantiate codomains ta,
                TypeEq.trans S.levels (TypeEq.instantiate codomainsLR ta) (TypeEq.of_instantiateEq tER' hv' ta firsts),
                ?_⟩
              intro piece member
              rcases List.mem_append.mp member with inPrefix | isLast
              · exact prefixHolds piece inPrefix
              · rw [List.mem_singleton.mp isLast]
                exact ⟨domainsLR, firsts⟩
  | @fst p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro U derivation tl tr typed
      cases derivation with
      | fst spinesInner =>
          cases spinesInner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
              obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
              obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
              obtain ⟨tqR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tq
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := ih prefixSpines tpL tqR typed
              have toSigmaL : TypeEq S.R Γ TL (.sigma AL BL) :=
                Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
              have toSigmaR : TypeEq S.R Γ TR (.sigma AR BR) :=
                Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tqR formed)
              obtain ⟨domains, _⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels atU red.typeEq))
              obtain ⟨domainsLR, _⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels prefixTypes toSigmaR))
              exact ⟨domains, domainsLR, prefixHolds⟩
  | @snd p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro U derivation tl tr typed
      cases derivation with
      | snd spinesInner =>
          cases spinesInner with
          | spinesW prefixSpines red _ =>
              obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
              obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
              obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
              obtain ⟨tqR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tq
              obtain ⟨atU, prefixTypes, prefixHolds⟩ := ih prefixSpines tpL tqR typed
              have toSigmaL : TypeEq S.R Γ TL (.sigma AL BL) :=
                Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
              have toSigmaR : TypeEq S.R Γ TR (.sigma AR BR) :=
                Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tqR formed)
              obtain ⟨_, codomains⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels atU red.typeEq))
              obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
                (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels prefixTypes toSigmaR))
              have tpSigma := Typed.convType tpL toSigmaL
              have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim tpSigma
              have firsts : Equal S.R Γ (.fst p) (.fst q) AL :=
                .fstCong (Equal.convType (inner.congr facts roots heads formed th prefixHolds) toSigmaL)
              obtain ⟨_, ⟨v', hv', tBR⟩⟩ := IsType.sigma_parts (isType_of_typeEq formed toSigmaR)
              have tBR' := Typed.stable tBR (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
              exact ⟨TypeEq.instantiate codomains tFst,
                TypeEq.trans S.levels (TypeEq.instantiate codomainsLR tFst)
                  (TypeEq.of_instantiateEq tBR' hv' tFst firsts), prefixHolds⟩

include facts roots heads algebra rigid complete in
/-- **Elimination spines of one variable decompose exactly at every type**, along types that reduce to Π and Σ
types: two typed spines read together are equal at a type exactly when every piece holds. The type need not be a base
type. -/
theorem ElimRel.exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n}
    {left right TL TR C : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR)
    (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
    fun U typed => Typed.generation typed
  obtain ⟨tlL, principalL, _⟩ := read.typed_left facts roots heads formed th principal tl
  obtain ⟨trR, _, _⟩ := read.swap.typed_left facts roots heads formed th principal tr
  have typed := read.pieces_typed facts roots heads formed th principal tl tr
  constructor
  · intro same
    obtain ⟨leftNeutral, rightNeutral⟩ := read.neutral (roles := S.roles) (.var h)
    obtain ⟨m, Δ, ρ, formedΔ, compatible, injective, U, spines⟩ :=
      descends (complete formed same) formed leftNeutral rightNeutral
    have renamed := read.rename ρ
    simp only [Presentation.rename] at renamed
    rw [← compatible h] at renamed
    have holds := (renamed.holds facts roots heads algebra formedΔ spines (tlL.rename compatible)
      (trR.rename compatible) (fun piece member => by
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact ⟨(typed original inside).1.rename compatible, (typed original inside).2.rename compatible⟩)).2.2
    intro piece member
    exact piece_reflects facts roots heads algebra rigid complete compatible injective formed formedΔ
      (typed piece member) (holds _ (List.mem_map.mpr ⟨piece, member, rfl⟩))
  · intro held
    exact .subEq (read.congr facts roots heads formed th held) (TypeLe.toBelow (principalL C tl) (Typed.isType tl formed))

end Theory

/-! ## The earlier readings are cases of this one -/

section Subsumes

variable {R : Rules Head}

/-- **Argument pieces of two application spines along reducts** are a reading, from any reading of the heads. -/
theorem ElimRel.of_argRel {n : Nat} {head type : Tm Head n} :
    ∀ {as bs : List (Tm Head n)} {f g TL TR F : Tm Head n} {before pieces : List (Piece Head n)},
      ElimRel R head type f g before TL TR → ArgRel R TL TR as bs pieces F →
      ∃ F', ElimRel R head type (appSpine f as) (appSpine g bs) (before ++ pieces) F F' := by
  intro as bs f g TL TR F before pieces start read
  induction read generalizing f g before with
  | nil TL TR => exact ⟨TR, by simpa using start⟩
  | @cons TL TR DL DR a b F EL ER as bs rest left right _ ih =>
      obtain ⟨F', inner⟩ := ih (.app start left right)
      exact ⟨F', by simpa [appSpine] using inner⟩

/-- **An equal projection above two readings** is a reading, when both types read reduce to Σ types. -/
theorem ElimRel.of_projection {n : Nat} {head type p q TL TR AL AR : Tm Head n} {BL BR : Tm Head (n + 1)}
    {pieces : List (Piece Head n)} (first : Bool) (read : ElimRel R head type p q pieces TL TR)
    (left : Reduces R TL (.sigma AL BL)) (right : Reduces R TR (.sigma AR BR)) :
    ∃ FL FR, ElimRel R head type (project first p) (project first q) pieces FL FR := by
  cases first with
  | true => exact ⟨_, _, .fst read left right⟩
  | false => exact ⟨_, _, .snd read left right⟩

/-- **The reader along literal types is a reading**: a literal Π or Σ type reduces to itself. -/
theorem ElimRel.of_elimParts {n : Nat} (Γ : Ctx Head n) :
    ∀ (left right : Tm Head n) {pieces : List (Piece Head n)} {TL TR : Tm Head n},
      elimParts Γ left right = some (pieces, TL, TR) →
      ∃ h, ElimRel R (.var h) (Ctx.lookup Γ h) left right pieces TL TR
  | .var h, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      simp only [elimParts] at found
      split at found
      · rename_i same
        subst same
        cases found
        exact ⟨h, .nil⟩
      · cases found
  | .app f a, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i g b
      obtain ⟨prefixPieces, DL, EL, DR, ER, read, result⟩ := appStep_some found
      cases result
      obtain ⟨h, inner⟩ := ElimRel.of_elimParts Γ f g read
      exact ⟨h, .app inner .refl .refl⟩
  | .fst p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := fstStep_some found
      cases result
      obtain ⟨h, inner⟩ := ElimRel.of_elimParts Γ p q read
      exact ⟨h, .fst inner .refl .refl⟩
  | .snd p, right, pieces, TL, TR, found => by
      cases right
      all_goals first | cases found | skip
      rename_i q
      obtain ⟨prefixPieces, AL, BL, AR, BR, read, result⟩ := sndStep_some found
      cases result
      obtain ⟨h, inner⟩ := ElimRel.of_elimParts Γ p q read
      exact ⟨h, .snd inner .refl .refl⟩
  | .const _, _, _, _, _, found => by cases found
  | .head _, _, _, _, _, found => by cases found
  | .pi _ _, _, _, _, _, found => by cases found
  | .sigma _ _, _, _, _, _, found => by cases found
  | .id _ _ _, _, _, _, _, found => by cases found
  | .lam _, _, _, _, _, found => by cases found
  | .pair _ _, _, _, _, _, found => by cases found
  | .refl _, _, _, _, _, found => by cases found

end Subsumes

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
