import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimRel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthBaseFamily

/-!
# The pieces of the elimination reading: reducts, stratification, weight

For two elimination spines of one variable read along reducts (`ElimRel`):

* **Miller reducts** (`ElimRel.reducts`): when the head is rigid and both spines have closed normal Miller reducts,
  so has every argument piece.
* **Stratification** (`ElimRel.internal`): the two domains of a piece are equal types once the pieces before it hold,
  and the two types read are equal once every piece holds.
* **Normal forms and weight** (`ElimRel.normal`, `ElimRel.weight`): the normal form of an elimination spine is an
  elimination spine of the normal forms of its arguments, so at a base type the two sides weigh at least two more
  than the pieces.
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
open ContextualDependentSpinesMany ContextualDependentDecisiveFragment ContextualDependentDynamicFragment
open ContextualDependentCumulativeClosure (MarkedReduct)
open ContextualDependentExecutableJoin (Elim)
open ContextualDependentEliminations (Piece.swap)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Miller reducts -/

section Reducts

variable {R : Rules Head}

/-- Both spines of a variable are elimination spines, with rigid heads when the variable is rigid. -/
theorem ElimRel.elims {n : Nat} {h : Fin n} {type left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    {mark : Fin n → Bool} (rigidHead : mark h = false) (read : ElimRel R (.var h) type left right pieces TL TR) :
    Elim left ∧ Elim right ∧ flexHead mark (spineHead left) = false ∧ flexHead mark (spineHead right) = false := by
  induction read with
  | nil => exact ⟨.var h, .var h, rigidHead, rigidHead⟩
  | app _ _ _ ih => exact ⟨.app ih.1, .app ih.2.1, ih.2.2.1, ih.2.2.2⟩
  | fst _ _ _ ih => exact ⟨.fst ih.1, .fst ih.2.1, rfl, rfl⟩
  | snd _ _ _ ih => exact ⟨.snd ih.1, .snd ih.2.1, rfl, rfl⟩

/-- **The arguments of two elimination spines of a rigid variable have Miller normal reducts** when the spines do. -/
theorem ElimRel.reducts (empty : R.computation = RootComputation.empty) {n : Nat} {h : Fin n}
    {type left right TL TR : Tm Head n} {pieces : List (Piece Head n)} {mark : Fin n → Bool}
    (rigidHead : mark h = false) (read : ElimRel R (.var h) type left right pieces TL TR) :
    MarkedReduct R mark left → MarkedReduct R mark right →
      ∀ piece ∈ pieces, MarkedReduct R mark piece.left ∧ MarkedReduct R mark piece.right := by
  induction read with
  | nil => exact fun _ _ _ member => by simp at member
  | @app f g a b TL TR DL DR EL ER pieces inner _ _ ih =>
      intro leftReduct rightReduct
      obtain ⟨elimF, elimG, headF, headG⟩ := inner.elims rigidHead
      obtain ⟨rf, ra⟩ := MarkedReduct.of_app empty elimF headF leftReduct
      obtain ⟨rg, rb⟩ := MarkedReduct.of_app empty elimG headG rightReduct
      intro piece member
      rcases List.mem_append.mp member with inPrefix | isLast
      · exact ih rf rg piece inPrefix
      · rw [List.mem_singleton.mp isLast]
        exact ⟨ra, rb⟩
  | @fst p q TL TR AL AR BL BR pieces inner _ _ ih =>
      intro leftReduct rightReduct
      obtain ⟨elimP, elimQ, _, _⟩ := inner.elims rigidHead
      exact ih (MarkedReduct.of_project empty true elimP leftReduct)
        (MarkedReduct.of_project empty true elimQ rightReduct)
  | @snd p q TL TR AL AR BL BR pieces inner _ _ ih =>
      intro leftReduct rightReduct
      obtain ⟨elimP, elimQ, _, _⟩ := inner.elims rigidHead
      exact ih (MarkedReduct.of_project empty false elimP leftReduct)
        (MarkedReduct.of_project empty false elimQ rightReduct)

end Reducts

/-! ## Stratification, normal forms, weight -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **Elimination spines are stratified along their prefixes**: the domains of a piece are equal types once the
pieces before it hold, and the two types read are equal once every piece holds. -/
theorem ElimRel.internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n}
    {left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR) :
    TypedEquality.Typed S.R Γ left TL → TypedEquality.Typed S.R Γ right TR →
      (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      (∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType) ∧
      ((∀ q ∈ pieces, q.Holds S.R Γ) → TypeEq S.R Γ TL TR) := by
  have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
    fun U typed => Typed.generation typed
  induction read with
  | nil =>
      intro tl _ _
      have isT := Typed.isType tl formed
      exact ⟨fun first last piece split => absurd split.symm (by simp), fun _ => isT.refl⟩
  | @app f g a b TL TR DL DR EL ER pieces inner redL redR ih =>
      intro tl tr typed
      obtain ⟨A₁, B₁, tf, _, _⟩ := Typed.generation tl
      obtain ⟨tfL, _, _⟩ := inner.typed_left facts roots heads formed th principal tf
      obtain ⟨A₂, B₂, tg, _, _⟩ := Typed.generation tr
      obtain ⟨tgR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tg
      obtain ⟨prefixInternal, prefixFinal⟩ := ih tfL tgR
        (fun piece member => typed piece (List.mem_append_left _ member))
      have toPiL : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tfL formed)
      have toPiR : TypeEq S.R Γ TR (.pi DR ER) :=
        Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tgR formed)
      have parts : TypeEq S.R Γ TL TR → TypeEq S.R Γ DL DR ∧ TypeEq S.R (.snoc Γ DL) EL ER := fun types =>
        (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
          (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels types toPiR))
      obtain ⟨ta, tb⟩ := typed _ (List.mem_append_right _ List.mem_cons_self)
      refine ⟨fun first last piece split held => ?_, fun held => ?_⟩
      · rcases List.eq_nil_or_concat last with rfl | ⟨middle, final, rfl⟩
        · obtain ⟨samePrefix, sameLast⟩ := List.append_inj' split (by simp)
          simp only [List.cons.injEq, and_true] at sameLast
          subst sameLast
          subst samePrefix
          exact (parts (prefixFinal held)).1
        · have split' : pieces ++ [⟨DL, a, DR, b⟩] = (first ++ piece :: middle) ++ [final] := by
            rw [split]
            simp
          obtain ⟨samePrefix, _⟩ := List.append_inj' split' (by simp)
          exact prefixInternal first middle piece samePrefix held
      · obtain ⟨domainsLR, codomainsLR⟩ :=
          parts (prefixFinal (fun q member => held q (List.mem_append_left _ member)))
        have firsts : Equal S.R Γ a b DL := (held _ (List.mem_append_right _ List.mem_cons_self)).2
        obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiR)
        have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
        exact TypeEq.trans S.levels (TypeEq.instantiate codomainsLR ta) (TypeEq.of_instantiateEq tER' hv' ta firsts)
  | @fst p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro tl tr typed
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
      obtain ⟨tqR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tq
      obtain ⟨prefixInternal, prefixFinal⟩ := ih tpL tqR typed
      have toSigmaL : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      have toSigmaR : TypeEq S.R Γ TR (.sigma AR BR) :=
        Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tqR formed)
      exact ⟨prefixInternal, fun held => ((ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
        (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels (prefixFinal held) toSigmaR))).1⟩
  | @snd p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro tl tr typed
      obtain ⟨A₁, B₁, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
      obtain ⟨A₂, B₂, tq, _⟩ := Typed.generation tr
      obtain ⟨tqR, _, _⟩ := inner.swap.typed_left facts roots heads formed th principal tq
      obtain ⟨prefixInternal, prefixFinal⟩ := ih tpL tqR typed
      have toSigmaL : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      have toSigmaR : TypeEq S.R Γ TR (.sigma AR BR) :=
        Reduces.typeEq (S := S) facts roots heads formed redR (Typed.isType tqR formed)
      refine ⟨prefixInternal, fun held => ?_⟩
      obtain ⟨domainsLR, codomainsLR⟩ := (ContextualDependentRigid.typeEq_sigma_iff facts formed).mp
        (TypeEq.trans S.levels (TypeEq.symm toSigmaL) (TypeEq.trans S.levels (prefixFinal held) toSigmaR))
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim (Typed.convType tpL toSigmaL)
      have firsts : Equal S.R Γ (.fst p) (.fst q) AL :=
        .fstCong (Equal.convType (inner.congr facts roots heads formed th held) toSigmaL)
      obtain ⟨_, ⟨v', hv', tBR⟩⟩ := IsType.sigma_parts (isType_of_typeEq formed toSigmaR)
      have tBR' := Typed.stable tBR (CtxEq.snoc (CtxEq.refl Γ formed) domainsLR)
      exact TypeEq.trans S.levels (TypeEq.instantiate codomainsLR tFst) (TypeEq.of_instantiateEq tBR' hv' tFst firsts)

include facts roots heads algebra rigid complete in
/-- **The normal form of an elimination spine** is an elimination spine of the normal forms of its arguments, and
weighs at least one more than they do. -/
theorem ElimRel.normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n}
    {left right TL TR : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR) :
    TypedEquality.Typed S.R Γ left TL →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) →
      ∃ (normal : Tm Head n) (ws : List Nat),
        ArgWeights S Γ (pieces.map (·.left)) (pieces.map (·.leftType)) ws ∧
        Long S.R S.roles (.spine Γ normal TL) ∧ Equal S.R Γ left normal TL ∧ ws.sum + 1 ≤ weight normal := by
  have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
    fun U typed => Typed.generation typed
  induction read with
  | nil =>
      intro tl _
      have isT := Typed.isType tl formed
      exact ⟨.var h, [], .nil, .var h isT.refl, .refl tl, by simp [weight]⟩
  | @app f g a b TL TR DL DR EL ER pieces inner redL redR ih =>
      intro tl typed
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation tl
      obtain ⟨tfL, _, _⟩ := inner.typed_left facts roots heads formed th principal tf
      obtain ⟨fn, ws, weights, longF, equalF, weighed⟩ := ih tfL
        (fun piece member => typed piece (List.mem_append_left _ member))
      have ta := typed _ (List.mem_append_right _ List.mem_cons_self)
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      have toPi : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tfL formed)
      obtain ⟨_, ⟨v, hv, tE⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPi)
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (inst0 a EL)) :=
        .app longF toPi nA.1 (TypeEq.of_instantiateEq tE hv ta nA.2)
      refine ⟨.app fn na, ws ++ [weight na], ?_, longApp,
        Derivable.appCong (Equal.convType equalF toPi) nA.2, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact ContextualDependentEliminations.ArgWeights.snoc weights ⟨na, nA, rfl⟩
      · simp only [weight, List.sum_append, List.sum_cons, List.sum_nil]
        omega
  | @fst p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro tl typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
      obtain ⟨pn, ws, weights, longP, equalP, weighed⟩ := ih tpL typed
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.sigma_parts (isType_of_typeEq formed toSigma)
      refine ⟨.fst pn, ws, weights, .fst longP toSigma (IsType.refl ⟨u, hu, tA⟩),
        .fstCong (Equal.convType equalP toSigma), ?_⟩
      simp only [weight]
      omega
  | @snd p q TL TR AL AR BL BR pieces inner redL redR ih =>
      intro tl typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨tpL, _, _⟩ := inner.typed_left facts roots heads formed th principal tp
      obtain ⟨pn, ws, weights, longP, equalP, weighed⟩ := ih tpL typed
      have toSigma : TypeEq S.R Γ TL (.sigma AL BL) :=
        Reduces.typeEq (S := S) facts roots heads formed redL (Typed.isType tpL formed)
      obtain ⟨_, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts (isType_of_typeEq formed toSigma)
      have equalSigma := Equal.convType equalP toSigma
      have tFst : TypedEquality.Typed S.R Γ (.fst p) AL := Derivable.fstElim (Typed.convType tpL toSigma)
      have firsts : Equal S.R Γ (.fst p) (.fst pn) AL := .fstCong equalSigma
      refine ⟨.snd pn, ws, weights, .snd longP toSigma (TypeEq.of_instantiateEq tB hv tFst firsts),
        .sndCong equalSigma, ?_⟩
      simp only [weight]
      omega

include facts roots heads algebra rigid complete in
/-- **Elimination spines weigh more than their pieces** at a base type: the decomposition lowers the normal weight
by at least two. -/
theorem ElimRel.weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n}
    {left right TL TR C : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ left C) (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
    fun U typed => Typed.generation typed
  have swapped := read.swap
  obtain ⟨tlL, principalL, leftTyped⟩ := read.typed_left facts roots heads formed th principal tl
  obtain ⟨trR, principalR, rightTyped⟩ := swapped.typed_left facts roots heads formed th principal tr
  obtain ⟨ln, ws, weights, longL, equalL, weighL⟩ :=
    read.normal facts roots heads algebra rigid complete formed tlL leftTyped
  obtain ⟨rn, ws', weights', longR, equalR, weighR⟩ :=
    swapped.normal facts roots heads algebra rigid complete formed trR rightTyped
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
  refine ⟨ws.sum + ws'.sum, ContextualDependentRank.weight ln, ContextualDependentRank.weight rn,
    ArgWeights.piecesOf (S := S) weights rightWeights,
    ⟨ln, normalL, rfl⟩, ⟨rn, normalR, rfl⟩, by omega⟩

end Theory

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
