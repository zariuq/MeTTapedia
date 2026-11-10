import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSkeletonFamily

/-!
# Spines of one local along the reducts of the instantiated types

R99's decomposition between spines of one local reads the local's type `h : Π (y₁ : D₁). E₁` literally: after each
argument the next type is the instantiation `E₁[a₁]`, which must again be a literal Π type. An instantiation can hide
the next binder behind a redex: `(λ x. x → U0) A` is the type of `h (λ x. x → U0)` for
`h : Π (G : U0 → U1). G A` (`ArgControls.argStore`). Abel and Pientka read the weak-head normal form of the type at
each argument.

* **The relational reading** (`ArgRel`, `DepRel`) asks each type only to *reduce* to a Π type. It is kept by every
  substitution that fixes the locals (`ArgRel.subst`, `DepRel.subst`), since reduction is, and it has the theory of
  the literal reading: typing at the domains read (`ArgRel.typed`, `DepRel.typed`), application congruence
  (`ArgRel.congr`), injectivity from the algorithmic comparison (`ArgRel.holds`), exactness
  (`argRel_exact`, `DepRel.exact`), normal forms and weight (`ArgRel.normal`, `argRel_weight`, `DepRel.weight`),
  stratification of the pieces among themselves (`ArgRel.internal`, `DepRel.internal`), and Miller reducts of the
  pieces (`DepRel.reducts`).
* **Projections.** Equal projections of two spines of one local, `fst (h ā) ≐ fst (h b̄)` (or `snd`), are read the
  same way (`DepRel.proj`): the algorithmic comparison compares them by their projected spines, so they decompose
  exactly into the argument pieces (`projRel_exact`), and their normal forms are the projections of the normal spines
  (`projRel_side`, `projRel_weight`).
* **The executable reading** (`argPartsN`, `dependentUnderN`) takes the reducer's reduct of every instantiated type
  (`normalCode`), at spines and at their projections (`baseShape`, `projShape`); it is a relational reading
  (`dependentUnderN_rel`) and eventually constant in the budget (`dependentUnderN_const`).
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
open ContextualDependentConstantHeadsProjections (project readProjection readProjection_spec subst_project
  project_generation project_congr project_neutral spines_project_inv)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Reducts at the budget -/

section NormalCodes

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
variable (reducer : ExecutableReduction.Reducer S.R)

/-- The reduct the reducer reaches at the budget, or the code itself. -/
def normalCode (fuel : Nat) {n : Nat} (code : Tm Head n) : Tm Head n :=
  (reducer fuel code).elim code Subtype.val

theorem normalCode_reduces (fuel : Nat) {n : Nat} (code : Tm Head n) :
    Reduces S.R code (normalCode reducer fuel code) := by
  unfold normalCode
  cases reducer fuel code with
  | some result => exact result.property
  | none => exact .refl

include facts roots heads in
theorem normalCode_typeEq (fuel : Nat) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {code : Tm Head n}
    (isType : IsType S.R Γ code) : TypeEq S.R Γ code (normalCode reducer fuel code) :=
  Reduces.typeEq (S := S) facts roots heads formed (normalCode_reduces reducer fuel code) isType

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  ContextualDependentConversionBudget.Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem reducer_keeps {n : Nat} (code : Tm Head n) {fuel larger : Nat}
    {result : ExecutableReduction.Result S.R code} (computed : reducer fuel code = some result)
    (enough : fuel ≤ larger) : reducer larger code = some result := by
  induction enough with
  | refl => exact computed
  | step _ ih => exact stable _ code result ih

include stable in
theorem normalCode_const {n : Nat} (code : Tm Head n) :
    EventuallyConst fun fuel => normalCode reducer fuel code :=
  EventuallyConst.comp (fun found : Option (ExecutableReduction.Result S.R code) => found.elim code Subtype.val)
    (EventuallyConst.of_mono fun computed enough => reducer_keeps reducer stable code computed enough)

end NormalCodes

/-! ## Argument pieces along types that reduce to Π types -/

/-- **The argument pieces of two spines along types that reduce to Π types**, with the final type of the left
spine. -/
inductive ArgRel (R : Rules Head) {n : Nat} :
    Tm Head n → Tm Head n → List (Tm Head n) → List (Tm Head n) → List (Piece Head n) → Tm Head n → Prop
  | nil (TL TR : Tm Head n) : ArgRel R TL TR [] [] [] TL
  | cons {TL TR DL DR a b F : Tm Head n} {EL ER : Tm Head (n + 1)} {as bs : List (Tm Head n)}
      {pieces : List (Piece Head n)} :
      Reduces R TL (.pi DL EL) → Reduces R TR (.pi DR ER) →
      ArgRel R (inst0 a EL) (inst0 b ER) as bs pieces F →
      ArgRel R TL TR (a :: as) (b :: bs) (⟨DL, a, DR, b⟩ :: pieces) F

namespace ArgRel

variable {R : Rules Head}

theorem sides {n : Nat} {TL TR F : Tm Head n} {as bs : List (Tm Head n)} {pieces : List (Piece Head n)}
    (read : ArgRel R TL TR as bs pieces F) : pieces.map (·.left) = as ∧ pieces.map (·.right) = bs := by
  induction read with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ ih => exact ⟨by simp [ih.1], by simp [ih.2]⟩

/-- The reading of the two spines the other way round. -/
theorem swap {n : Nat} {TL TR F : Tm Head n} {as bs : List (Tm Head n)} {pieces : List (Piece Head n)}
    (read : ArgRel R TL TR as bs pieces F) :
    ∃ F', ArgRel R TR TL bs as (pieces.map fun piece => ⟨piece.rightType, piece.right, piece.leftType, piece.left⟩)
      F' := by
  induction read with
  | nil TL TR => exact ⟨TR, .nil TR TL⟩
  | cons left right _ ih =>
      obtain ⟨F', inner⟩ := ih
      exact ⟨F', .cons right left inner⟩

/-- **The reading is kept by every substitution.** -/
theorem subst {n m : Nat} (σ : Sub Head n m) {TL TR F : Tm Head n} {as bs : List (Tm Head n)}
    {pieces : List (Piece Head n)} (read : ArgRel R TL TR as bs pieces F) :
    ArgRel R (Presentation.subst σ TL) (Presentation.subst σ TR) (as.map (Presentation.subst σ))
      (bs.map (Presentation.subst σ)) (pieces.map (Piece.subst σ)) (Presentation.subst σ F) := by
  induction read generalizing m with
  | nil TL TR => exact .nil _ _
  | cons left right _ ih =>
      have inner := ih σ
      rw [subst_inst0, subst_inst0] at inner
      exact .cons (Reduces.substitute left σ) (Reduces.substitute right σ) inner

end ArgRel

/-! ## Typing, congruence, injectivity, normal forms -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

theorem isType_of_typeEq {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A B : Tm Head n}
    (equal : TypeEq S.R Γ A B) : IsType S.R Γ B := by
  obtain ⟨u, hu, e⟩ := equal
  exact ⟨u, hu, (Equal.typed e formed).2⟩

include facts roots heads in
/-- **A spine along types that reduce to Π types**: when the head's type is below every type of the head, a typed
spine has its arguments at the domains read, and its final type is below the spine's type. -/
theorem ArgRel.typed_left {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {as bs : List (Tm Head n)} {TL TR F : Tm Head n} {pieces : List (Piece Head n)}
    (read : ArgRel S.R TL TR as bs pieces F) :
    ∀ {f C : Tm Head n}, (∀ U, TypedEquality.Typed S.R Γ f U → TypeLe S.R Γ TL U) →
      TypedEquality.Typed S.R Γ f TL → TypedEquality.Typed S.R Γ (appSpine f as) C →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) ∧ TypeLe S.R Γ F C := by
  induction read with
  | nil TL TR =>
      intro f C principal _ typed
      exact ⟨fun _ member => by simp at member, principal C typed⟩
  | @cons TL TR DL DR a b F EL ER as bs rest left right inner ih =>
      intro f C principal tf typed
      have toPi : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed left (Typed.isType tf formed)
      have lePi : ∀ {U}, TypeLe S.R Γ TL U → TypeLe S.R Γ (.pi DL EL) U := fun le => by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toPi
        exact .conv e hu le
      obtain ⟨U, prefixTyped⟩ := appSpine_prefix_typed (t := .app f a) as typed
      obtain ⟨A, B, tf', ta, _⟩ := Typed.generation prefixTyped
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (lePi (principal _ tf')) (Typed.isType tf' formed) formed
      have ta' : TypedEquality.Typed S.R Γ a DL := Typed.convType ta domains.symm
      have principal' : ∀ U, TypedEquality.Typed S.R Γ (.app f a) U → TypeLe S.R Γ (inst0 a EL) U := by
        intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (lePi (principal _ tf'')) (Typed.isType tf'' formed) formed
        have instantiated : Below S.R Γ (inst0 a EL) (inst0 a B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        exact .sub instantiated le'
      obtain ⟨args, final⟩ := ih principal' (Derivable.appElim (Typed.convType tf toPi) ta') typed
      refine ⟨fun piece member => ?_, final⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact ta'
      · exact args piece later

include facts roots heads in
/-- **Both spines' arguments are typed at their own domains.** -/
theorem ArgRel.typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {as bs : List (Tm Head n)}
    {TL TR F f g C : Tm Head n} {pieces : List (Piece Head n)} (read : ArgRel S.R TL TR as bs pieces F)
    (principalL : ∀ U, TypedEquality.Typed S.R Γ f U → TypeLe S.R Γ TL U) (tf : TypedEquality.Typed S.R Γ f TL)
    (principalR : ∀ U, TypedEquality.Typed S.R Γ g U → TypeLe S.R Γ TR U) (tg : TypedEquality.Typed S.R Γ g TR)
    (tl : TypedEquality.Typed S.R Γ (appSpine f as) C) (tr : TypedEquality.Typed S.R Γ (appSpine g bs) C) :
    (∀ piece ∈ pieces, piece.Typed S.R Γ) ∧ TypeLe S.R Γ F C := by
  obtain ⟨left, final⟩ := read.typed_left facts roots heads formed principalL tf tl
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨right, _⟩ := swapped.typed_left facts roots heads formed principalR tg tr
  refine ⟨fun piece member => ⟨left piece member, ?_⟩, final⟩
  exact right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)

include facts roots heads in
/-- **Application congruence along the left types read.** -/
theorem ArgRel.congr {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {as bs : List (Tm Head n)}
    {TL TR F : Tm Head n} {pieces : List (Piece Head n)} (read : ArgRel S.R TL TR as bs pieces F) :
    ∀ {f g : Tm Head n}, IsType S.R Γ TL → (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      (∀ piece ∈ pieces, piece.Holds S.R Γ) → Equal S.R Γ f g TL →
      Equal S.R Γ (appSpine f as) (appSpine g bs) F := by
  induction read with
  | nil => intro f g _ _ _ same; exact same
  | @cons TL TR DL DR a b F EL ER as bs rest left right inner ih =>
      intro f g isTL typed held same
      have toPi : TypeEq S.R Γ TL (.pi DL EL) := Reduces.typeEq (S := S) facts roots heads formed left isTL
      obtain ⟨_, ⟨v, hv, tEL⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPi)
      have ta := (typed _ List.mem_cons_self).1
      exact ih ⟨v, hv, Typed.instantiate tEL ta⟩ (fun piece member => typed piece (List.mem_cons_of_mem _ member))
        (fun piece member => held piece (List.mem_cons_of_mem _ member))
        (Derivable.appCong (Equal.convType same toPi) (held _ List.mem_cons_self).2)

include facts roots heads algebra in
/-- **Along types that reduce to Π types, the compared arguments make the pieces hold.** -/
theorem ArgRel.holds {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {as bs : List (Tm Head n)}
    {TL TR F : Tm Head n} {pieces : List (Piece Head n)} (read : ArgRel S.R TL TR as bs pieces F) :
    ∀ {T U : Tm Head n}, SpineArgs S Γ T as bs U → TypeEq S.R Γ TL T → TypeEq S.R Γ TL TR →
      IsType S.R Γ TL → IsType S.R Γ TR → (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  induction read with
  | nil => intro _ _ _ _ _ _ _ _ piece member; simp at member
  | @cons TL TR DL DR a b F EL ER as bs rest left right inner ih =>
      intro T U args sameT types isL isR typed
      cases args with
      | cons red terms others =>
          have toPiL : TypeEq S.R Γ TL (.pi DL EL) := Reduces.typeEq (S := S) facts roots heads formed left isL
          have toPiR : TypeEq S.R Γ TR (.pi DR ER) := Reduces.typeEq (S := S) facts roots heads formed right isR
          have toA := RedTy.typeEq red
          obtain ⟨domainsA, codomainsA⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
            (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels sameT toA))
          obtain ⟨domains, codomains⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
            (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels types toPiR))
          obtain ⟨ta, tb⟩ := typed _ List.mem_cons_self
          have firsts : Equal S.R Γ a b DL :=
            Equal.convType (Algorithmic.sound_terms facts roots heads algebra formed terms) (TypeEq.symm domainsA)
          obtain ⟨_, ⟨v, hv, tEL⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiL)
          obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiR)
          have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domains)
          have nextTypes : TypeEq S.R Γ (inst0 a EL) (inst0 b ER) :=
            TypeEq.trans S.levels (TypeEq.instantiate codomains ta)
              (TypeEq.of_instantiateEq tER' hv' ta firsts)
          intro piece member
          rcases List.mem_cons.mp member with rfl | later
          · exact ⟨domains, firsts⟩
          · exact ih others (TypeEq.instantiate codomainsA ta) nextTypes ⟨v, hv, Typed.instantiate tEL ta⟩
              ⟨v', hv', Typed.instantiate tER tb⟩ (fun other inside => typed other (List.mem_cons_of_mem _ inside))
              piece later

include facts roots heads algebra rigid complete in
/-- **The normal form of a spine along types that reduce to Π types** has the normal forms of the arguments. -/
theorem ArgRel.normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {as bs : List (Tm Head n)}
    {TL TR F : Tm Head n} {pieces : List (Piece Head n)} (read : ArgRel S.R TL TR as bs pieces F) :
    ∀ {f fn : Tm Head n}, Long S.R S.roles (.spine Γ fn TL) → Equal S.R Γ f fn TL →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) →
      ∃ (ns : List (Tm Head n)) (ws : List Nat),
        ArgWeights S Γ as (pieces.map (·.leftType)) ws ∧
        Long S.R S.roles (.spine Γ (appSpine fn ns) F) ∧
        Equal S.R Γ (appSpine f as) (appSpine fn ns) F ∧
        weight (appSpine fn ns) = weight fn + ws.sum + pieces.length := by
  induction read with
  | nil => intro f fn long same _; exact ⟨[], [], .nil, long, same, by simp⟩
  | @cons TL TR DL DR a b F EL ER as bs rest left right inner ih =>
      intro f fn long same typed
      have toPi : TypeEq S.R Γ TL (.pi DL EL) :=
        Reduces.typeEq (S := S) facts roots heads formed left (Typed.isType long.spine_typed formed)
      have ta := typed _ List.mem_cons_self
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      obtain ⟨_, ⟨v, hv, tE⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPi)
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (inst0 a EL)) :=
        .app long toPi nA.1 (TypeEq.of_instantiateEq tE hv ta nA.2)
      have applied : Equal S.R Γ (.app f a) (.app fn na) (inst0 a EL) :=
        Derivable.appCong (Equal.convType same toPi) nA.2
      obtain ⟨ns, ws, weights, longRest, equalRest, weighed⟩ := ih longApp applied
        (fun piece member => typed piece (List.mem_cons_of_mem _ member))
      refine ⟨na :: ns, weight na :: ws, .cons ⟨na, nA, rfl⟩ weights, longRest, equalRest, ?_⟩
      change weight (appSpine (.app fn na) ns) = _
      rw [weighed]
      simp only [ContextualDependentRank.weight, List.sum_cons, List.length_cons]
      omega

include facts roots heads in
/-- **Along two types that reduce to Π types and are equal, the domains of a piece are equal once the pieces before
it hold.** -/
theorem ArgRel.internal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {as bs : List (Tm Head n)}
    {TL TR F : Tm Head n} {pieces : List (Piece Head n)} (read : ArgRel S.R TL TR as bs pieces F) :
    TypeEq S.R Γ TL TR → IsType S.R Γ TL → IsType S.R Γ TR → (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  induction read with
  | nil => intro _ _ _ _ first last piece split _; exact absurd split.symm (by simp)
  | @cons TL TR DL DR a b F EL ER as bs rest left right inner ih =>
      intro types isL isR typed first last piece split held
      have toPiL : TypeEq S.R Γ TL (.pi DL EL) := Reduces.typeEq (S := S) facts roots heads formed left isL
      have toPiR : TypeEq S.R Γ TR (.pi DR ER) := Reduces.typeEq (S := S) facts roots heads formed right isR
      obtain ⟨domains, codomains⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp
        (TypeEq.trans S.levels (TypeEq.symm toPiL) (TypeEq.trans S.levels types toPiR))
      rcases first with _ | ⟨one, first⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, -⟩ := split
        exact domains
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, split⟩ := split
        obtain ⟨ta, tb⟩ := typed _ List.mem_cons_self
        have firsts : Equal S.R Γ a b DL := (held _ List.mem_cons_self).2
        obtain ⟨_, ⟨v, hv, tEL⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiL)
        obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts (isType_of_typeEq formed toPiR)
        have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domains)
        have nextTypes : TypeEq S.R Γ (inst0 a EL) (inst0 b ER) :=
          TypeEq.trans S.levels (TypeEq.instantiate codomains ta) (TypeEq.of_instantiateEq tER' hv' ta firsts)
        exact ih nextTypes ⟨v, hv, Typed.instantiate tEL ta⟩ ⟨v', hv', Typed.instantiate tER tb⟩
          (fun other member => typed other (List.mem_cons_of_mem _ member)) first last piece split
          (fun q member => held q (List.mem_cons_of_mem _ member))

include facts roots heads algebra complete in
/-- **Spines of a local decompose exactly along types that reduce to Π types**, at a base type. -/
theorem argRel_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F) (nonempty : as ≠ []) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) (tr : TypedEquality.Typed S.R Γ (appSpine (.var h) bs) C) :
    Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨typed, final⟩ := read.typed facts roots heads formed principal th principal th tl tr
  obtain ⟨sameL, sameR⟩ := read.sides
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨U, spines⟩ := terms_spine_inv h base nonempty length (complete formed same)
    have args := spines_inv (S := S) h as bs length spines
    rw [headType] at args
    exact read.holds facts roots heads algebra formed args isT.refl isT.refl isT isT typed
  · intro held
    exact .subEq (read.congr facts roots heads formed isT typed held (.refl th))
      (TypeLe.toBelow final (Typed.isType tl formed))

include facts roots heads algebra rigid complete in
/-- **Spines of a local weigh more than their argument pieces**, along types that reduce to Π types. -/
theorem argRel_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) (tr : TypedEquality.Typed S.R Γ (appSpine (.var h) bs) C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ (appSpine (.var h) as) C wl ∧
      HasWeight S Γ (appSpine (.var h) bs) C wr ∧ w + 2 ≤ wl + wr := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  have longHead : Long S.R S.roles (.spine Γ (.var h) T) := by
    refine .var h ?_
    rw [headType]
    exact IsType.refl (Typed.isType th formed)
  have baseC := BaseType.base facts formed base
  have side : ∀ {cs ds : List (Tm Head n)} {readPieces : List (Piece Head n)} {F' : Tm Head n},
      ArgRel S.R T T cs ds readPieces F' → TypedEquality.Typed S.R Γ (appSpine (.var h) cs) C →
      TypedEquality.Typed S.R Γ (appSpine (.var h) ds) C →
      ∃ ws, ArgWeights S Γ cs (readPieces.map (·.leftType)) ws ∧
        HasWeight S Γ (appSpine (.var h) cs) C (1 + ws.sum + readPieces.length) := by
    intro cs ds readPieces F' reading typedC typedD
    obtain ⟨typed, final⟩ := reading.typed facts roots heads formed principal th principal th typedC typedD
    obtain ⟨ns, ws, weights, longSpine, equalSpine, weighed⟩ :=
      reading.normal facts roots heads algebra rigid complete formed longHead (.refl th)
        (fun piece member => (typed piece member).1)
    have below := TypeLe.toBelow final (Typed.isType typedC formed)
    have equalC : Equal S.R Γ (appSpine (.var h) cs) (appSpine (.var h) ns) C := .subEq equalSpine below
    refine ⟨ws, weights, appSpine (.var h) ns,
      ⟨.neutral longSpine below (Equal.typed equalC formed).2 baseC, equalC⟩, ?_⟩
    rw [weighed]
    simp only [ContextualDependentRank.weight]
    try omega
  obtain ⟨sameL, sameR⟩ := read.sides
  obtain ⟨ws, weights, left⟩ := side read tl tr
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨ws', weights', right⟩ := side swapped tr tl
  rw [← sameL] at weights
  rw [List.map_map, ← sameR] at weights'
  have pieces := ArgWeights.piecesOf (S := S) weights (by simpa [Function.comp_def] using weights')
  refine ⟨ws.sum + ws'.sum, _, _, pieces, left, right, ?_⟩
  simp only [List.length_map]
  omega

end Theory

/-! ## Dependent spines of one local under abstractions -/

/-- **Dependent spines of one local under abstractions, along types that reduce to Π types.** -/
inductive DepRel (R : Rules Head) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n →
    List (Piece Head n) → Prop
  | under {n : Nat} {locals : List (Tm Head n)} {D : Tm Head n} {T l r : Tm Head (n + 1)}
      {pieces : List (Piece Head (n + 1))} :
      DepRel R (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r pieces →
      DepRel R locals (.pi D T) (.lam l) (.lam r) (pieces.map (Piece.under D))
  | base {n : Nat} {locals : List (Tm Head n)} {C : Tm Head n} {h : Fin n} {as bs : List (Tm Head n)}
      {T F : Tm Head n} {pieces : List (Piece Head n)} :
      rigidBase locals.length C = true → h.val < locals.length → as ≠ [] → locals[h.val]? = some T →
      ArgRel R T T as bs pieces F →
      DepRel R locals C (appSpine (.var h) as) (appSpine (.var h) bs) pieces
  | proj {n : Nat} {locals : List (Tm Head n)} {C : Tm Head n} {h : Fin n} {first : Bool}
      {as bs : List (Tm Head n)} {T F : Tm Head n} {pieces : List (Piece Head n)} :
      rigidBase locals.length C = true → h.val < locals.length → as ≠ [] → locals[h.val]? = some T →
      ArgRel R T T as bs pieces F →
      DepRel R locals C (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs)) pieces

section ProjTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **The argument pieces of two projections of spines are typed.** -/
theorem projRel_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨A, B, tp, _⟩ := project_generation tl
  obtain ⟨A', B', tq, _⟩ := project_generation tr
  obtain ⟨left, _⟩ := read.typed_left facts roots heads formed principal th tp
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨right, _⟩ := swapped.typed_left facts roots heads formed principal th tq
  exact fun piece member => ⟨left piece member, right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩

include facts roots heads algebra complete in
/-- **Projections of spines of one local decompose exactly** along types that reduce to Π types, at a base type. -/
theorem projRel_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    Equal S.R Γ (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs)) C ↔
      ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨A, B, tp, le⟩ := project_generation tl
  obtain ⟨A', B', tq, _⟩ := project_generation tr
  obtain ⟨left, final⟩ := read.typed_left facts roots heads formed principal th tp
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨right, _⟩ := swapped.typed_left facts roots heads formed principal th tq
  have typed : ∀ piece ∈ pieces, piece.Typed S.R Γ := fun piece member =>
    ⟨left piece member, right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)⟩
  obtain ⟨sameL, sameR⟩ := read.sides
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨U, spines⟩ := ContextualDependentFragmentDecisive.terms_neutral_spines base
      (project_neutral first (neutral_appSpine h as)) (project_neutral first (neutral_appSpine h bs))
      (complete formed same)
    obtain ⟨U', prefixSpines⟩ := spines_project_inv first spines
    have args := spines_inv (S := S) h as bs length prefixSpines
    rw [headType] at args
    exact read.holds facts roots heads algebra formed args isT.refl isT.refl isT isT typed
  · intro held
    have congr := read.congr facts roots heads formed isT typed held (.refl th)
    have atSigma : Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) (.sigma A B) :=
      .subEq congr (TypeLe.toBelow final (Typed.isType tp formed))
    exact project_congr atSigma le (Typed.isType tl formed)

include facts roots heads algebra rigid complete in
/-- **The normal form of a projection of a spine** is the projection of the normal spine. -/
theorem projRel_side {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {cs ds : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (reading : ArgRel S.R T T cs ds pieces F) (base : BaseType S C)
    (typedC : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) cs)) C) :
    ∃ ws, ArgWeights S Γ cs (pieces.map (·.leftType)) ws ∧
      HasWeight S Γ (project first (appSpine (.var h) cs)) C (2 + ws.sum + pieces.length) := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  have longHead : Long S.R S.roles (.spine Γ (.var h) T) := by
    refine .var h ?_
    rw [headType]
    exact IsType.refl (Typed.isType th formed)
  have baseC := BaseType.base facts formed base
  have isC := Typed.isType typedC formed
  obtain ⟨A₀, B₀, tp, le⟩ := project_generation typedC
  obtain ⟨typed, final⟩ := reading.typed_left facts roots heads formed principal th tp
  obtain ⟨ns, ws, weights, longSpine, equalSpine, weighed⟩ :=
    reading.normal facts roots heads algebra rigid complete formed longHead (.refl th) typed
  have isSigma := Typed.isType tp formed
  have belowSigma := TypeLe.toBelow final isSigma
  obtain ⟨A, B, eF, leA, leB⟩ := Below.sigma_inv facts belowSigma formed (IsType.refl isSigma)
  have atSigma : Equal S.R Γ (appSpine (.var h) cs) (appSpine (.var h) ns) (.sigma A₀ B₀) :=
    .subEq equalSpine belowSigma
  have equalC := project_congr atSigma le isC
  have typedN := (Equal.typed equalC formed).2
  have isAB : IsType S.R Γ (.sigma A B) := by
    obtain ⟨uF, huF, eqF⟩ := eF
    exact ⟨uF, huF, (Equal.typed eqF formed).2⟩
  obtain ⟨⟨u, hu, tA⟩, ⟨v, hv, tB⟩⟩ := IsType.sigma_parts isAB
  have nSigma : TypedEquality.Typed S.R Γ (appSpine (.var h) ns) (.sigma A B) :=
    Typed.convType longSpine.spine_typed eF
  refine ⟨ws, weights, project first (appSpine (.var h) ns), ⟨?_, equalC⟩, ?_⟩
  · cases first with
    | true =>
        have longFst : Long S.R S.roles (.spine Γ (.fst (appSpine (.var h) ns)) A) :=
          .fst longSpine eF (IsType.refl ⟨u, hu, tA⟩)
        exact .neutral longFst (.subTrans leA (TypeLe.toBelow le isC)) typedN baseC
    | false =>
        have tFst : TypedEquality.Typed S.R Γ (.fst (appSpine (.var h) ns)) A := Derivable.fstElim nSigma
        have isU : IsType S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B) := ⟨v, hv, Typed.instantiate tB tFst⟩
        have longSnd : Long S.R S.roles
            (.spine Γ (.snd (appSpine (.var h) ns)) (inst0 (.fst (appSpine (.var h) ns)) B)) :=
          .snd longSpine eF (IsType.refl isU)
        obtain ⟨⟨u₀, hu₀, tA₀⟩, ⟨v₀, hv₀, tB₀⟩⟩ := IsType.sigma_parts isSigma
        have tFst₀ : TypedEquality.Typed S.R Γ (.fst (appSpine (.var h) ns)) A₀ := .sub tFst leA
        have stepB : Below S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B) (inst0 (.fst (appSpine (.var h) ns)) B₀) :=
          Derivable.substitutes leB (SubstMor.single tFst)
        have firsts : Equal S.R Γ (.fst (appSpine (.var h) ns)) (.fst (appSpine (.var h) cs)) A₀ :=
          .symm (.fstCong atSigma)
        have stepEq : TypeEq S.R Γ (inst0 (.fst (appSpine (.var h) ns)) B₀)
            (inst0 (.fst (appSpine (.var h) cs)) B₀) :=
          TypeEq.of_instantiateEq tB₀ hv₀ tFst₀ firsts
        exact .neutral longSnd (.subTrans stepB (.subTrans stepEq.below (TypeLe.toBelow le isC))) typedN baseC
  · cases first <;>
    · simp only [project, ContextualDependentRank.weight, weighed]
      omega

include facts roots heads algebra rigid complete in
/-- **Projections of spines of one local weigh more than their argument pieces.** -/
theorem projRel_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as bs : List (Tm Head n)} {T C F : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (read : ArgRel S.R T T as bs pieces F) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C)
    (tr : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) bs)) C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ (project first (appSpine (.var h) as)) C wl ∧
      HasWeight S Γ (project first (appSpine (.var h) bs)) C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨sameL, sameR⟩ := read.sides
  obtain ⟨ws, weights, left⟩ :=
    projRel_side facts roots heads algebra rigid complete formed h first headType read base tl
  obtain ⟨F', swapped⟩ := read.swap
  obtain ⟨ws', weights', right⟩ :=
    projRel_side facts roots heads algebra rigid complete formed h first headType swapped base tr
  rw [← sameL] at weights
  rw [List.map_map, ← sameR] at weights'
  have pieces := ArgWeights.piecesOf (S := S) weights (by simpa [Function.comp_def] using weights')
  refine ⟨ws.sum + ws'.sum, _, _, pieces, left, right, ?_⟩
  simp only [List.length_map]
  omega

end ProjTheory

section DepTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads in
/-- **The pieces of dependent spines under abstractions are typed.** -/
theorem DepRel.typed {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel S.R locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  induction read with
  | @under n locals D T l r inner _ ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have below := ih (formed.snoc ⟨u, hu, tD⟩) (types.under D) (Typed.lam_inv facts tl formed)
        (Typed.lam_inv facts tr formed)
      intro piece member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
  | @base n locals C h as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
        intro U typed
        have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
        rwa [headType] at le
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typed
      exact (read.typed facts roots heads formed principal th principal th tl tr).1
  | @proj n locals C h first as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_typed facts roots heads formed h first (types.head looked) read tl tr

include facts roots heads algebra complete in
/-- **Dependent spines under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem DepRel.exact {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel S.R locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ) := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      have below := ih formedD (types.under D) tl' tr'
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
      obtain ⟨w, hw, tPi⟩ := Typed.isType tl formed
      constructor
      · intro same piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact (Piece.holds_under facts formed isD (typed original inside)).mpr
          (below.mp (lam_equal_inv facts formed same) original inside)
      · intro held
        exact .lamCong tPi hw (below.mpr fun original inside =>
          (Piece.holds_under facts formed isD (typed original inside)).mp
            (held _ (List.mem_map.mpr ⟨original, inside, rfl⟩)))
  | @base n locals C h as bs T F pieces base _ nonempty looked read =>
      intro Γ formed types tl tr
      exact argRel_exact facts roots heads algebra complete formed h (types.head looked) read nonempty
        (rigidBase_spec base) tl tr
  | @proj n locals C h first as bs T F pieces base _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_exact facts roots heads algebra complete formed h first (types.head looked) read
        (rigidBase_spec base) tl tr

include facts roots heads algebra rigid complete in
/-- **Dependent spines under abstractions weigh more than their pieces.** -/
theorem DepRel.weight {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel S.R locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧
        HasWeight S Γ right annotation wr ∧ w + 2 ≤ wl + wr := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      obtain ⟨w, wl, wr, weighs, left, right, total⟩ := ih formedD (types.under D) tl' tr'
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
      obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
      exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
        HasWeight.under (w := v) hv tPi isD right, total⟩
  | @base n locals C h as bs T F pieces base _ _ looked read =>
      intro Γ formed types tl tr
      exact argRel_weight facts roots heads algebra rigid complete formed h (types.head looked) read
        (rigidBase_spec base) tl tr
  | @proj n locals C h first as bs T F pieces base _ _ looked read =>
      intro Γ formed types tl tr
      exact projRel_weight facts roots heads algebra rigid complete formed h first (types.head looked) read
        (rigidBase_spec base) tl tr

include facts roots heads in
/-- **The pieces of dependent spines under abstractions are stratified among themselves.** -/
theorem DepRel.internal {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel S.R locals annotation left right pieces) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∀ (first last : List (Piece Head n)) (piece : Piece Head n), pieces = first ++ piece :: last →
        (∀ q ∈ first, q.Holds S.R Γ) → TypeEq S.R Γ piece.leftType piece.rightType := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro Γ formed types tl tr first last piece split held
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
      have formedD := formed.snoc isD
      have tl' := Typed.lam_inv facts tl formed
      have tr' := Typed.lam_inv facts tr formed
      have typed := reading.typed facts roots heads formedD (types.under D) tl' tr'
      obtain ⟨first', rest', innerSplit, rfl, mapped⟩ := List.map_eq_append_iff.mp split
      obtain ⟨piece', last', rfl, rfl, rfl⟩ := List.map_eq_cons_iff.mp mapped
      have held' : ∀ q ∈ first', q.Holds S.R (.snoc Γ D) := fun q member =>
        (Piece.holds_under facts formed isD (typed q (by rw [innerSplit]; exact List.mem_append_left _ member))).mp
          (held (q.under D) (List.mem_map.mpr ⟨q, member, rfl⟩))
      have below := ih formedD (types.under D) tl' tr' first' last' piece' innerSplit held'
      exact (ContextualDependentRigid.typeEq_pi_iff facts formed).mpr ⟨isD.refl, below⟩
  | @base n locals C h as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
        intro U typed
        have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
        rwa [headType] at le
      have typed := (read.typed facts roots heads formed principal th principal th tl tr).1
      have isT := Typed.isType th formed
      exact read.internal facts roots heads formed isT.refl isT isT typed
  | @proj n locals C h first as bs T F pieces _ _ _ looked read =>
      intro Γ formed types tl tr
      have headType := types.head looked
      have th : TypedEquality.Typed S.R Γ (.var h) T := by
        have typedVar : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have typed := projRel_typed facts roots heads formed h first headType read tl tr
      have isT := Typed.isType th formed
      exact read.internal facts roots heads formed isT.refl isT isT typed

end DepTheory

/-- **The reading is kept by substitutions that fix the locals.** -/
theorem DepRel.subst {R : Rules Head} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel R locals annotation left right pieces) :
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      DepRel R (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) (pieces.map (Piece.subst σ)) := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro m σ fixes bound
      have below := ih (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
      have localsSame : (Presentation.rename wk D :: locals.map (Presentation.rename wk)).map
          (Presentation.subst (liftSub σ)) =
          Presentation.rename wk (Presentation.subst σ D) :: (locals.map (Presentation.subst σ)).map
            (Presentation.rename wk) := by
        rw [List.map_cons, subst_liftSub_wk, List.map_map, List.map_map]
        congr 1
        congr 1
        funext t
        exact subst_liftSub_wk σ t
      rw [localsSame] at below
      have mapped : (inner.map (Piece.under D)).map (Piece.subst σ) =
          (inner.map (Piece.subst (liftSub σ))).map (Piece.under (Presentation.subst σ D)) := by
        simp only [List.map_map]
        rfl
      rw [mapped]
      exact .under below
  | @base n locals C h as bs T F pieces base small nonempty looked read =>
      intro m σ fixes bound
      have hm : h.val < m := by omega
      have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
      rw [subst_appSpine, subst_appSpine]
      simp only [Presentation.subst, fixedHead]
      refine .base (h := ⟨h.val, hm⟩) (T := Presentation.subst σ T) (F := Presentation.subst σ F) ?_ ?_ ?_ ?_
        (read.subst σ)
      · rw [List.length_map]
        exact rigidBase_subst fixes bound base
      · simpa using small
      · simpa using nonempty
      · simp only [List.getElem?_map, looked, Option.map_some]
  | @proj n locals C h first as bs T F pieces base small nonempty looked read =>
      intro m σ fixes bound
      have hm : h.val < m := by omega
      have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
      rw [subst_project, subst_project, subst_appSpine, subst_appSpine]
      simp only [Presentation.subst, fixedHead]
      refine .proj (h := ⟨h.val, hm⟩) (T := Presentation.subst σ T) (F := Presentation.subst σ F) ?_ ?_ ?_ ?_
        (read.subst σ)
      · rw [List.length_map]
        exact rigidBase_subst fixes bound base
      · simpa using small
      · simpa using nonempty
      · simp only [List.getElem?_map, looked, Option.map_some]

/-- **The pieces of spines of one local have Miller normal reducts** when the two sides do, the locals rigid. -/
theorem DepRel.reducts (empty : S.R.computation = RootComputation.empty) {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : DepRel S.R locals annotation left right pieces) :
    ∀ (mark : Fin n → Bool), (∀ j : Fin n, j.val < locals.length → mark j = false) →
      ContextualDependentCumulativeClosure.MarkedReduct S.R mark left →
      ContextualDependentCumulativeClosure.MarkedReduct S.R mark right →
      ∀ piece ∈ pieces, ContextualDependentCumulativeClosure.MarkedReduct S.R mark piece.left ∧
        ContextualDependentCumulativeClosure.MarkedReduct S.R mark piece.right := by
  induction read with
  | @under n locals D T l r inner reading ih =>
      intro mark localsRigid leftReduct rightReduct
      have lifted : ∀ j : Fin (n + 1),
          j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
            ContextualDependentGeneralPattern.liftFlexible mark j = false := by
        intro j
        refine Fin.cases (motive := fun j : Fin (n + 1) =>
          j.val < (Presentation.rename wk D :: locals.map (Presentation.rename wk)).length →
            ContextualDependentGeneralPattern.liftFlexible mark j = false) ?_ (fun j small => ?_) j
        · intro _
          rfl
        · change mark j = false
          simp only [List.length_cons, List.length_map, Fin.val_succ] at small
          exact localsRigid j (by omega)
      intro piece member
      obtain ⟨original, inInner, rfl⟩ := List.mem_map.mp member
      obtain ⟨pl, pr⟩ := ih (ContextualDependentGeneralPattern.liftFlexible mark) lifted
        (ContextualDependentCumulativeClosure.MarkedReduct.of_lam empty leftReduct)
        (ContextualDependentCumulativeClosure.MarkedReduct.of_lam empty rightReduct) original inInner
      exact ⟨ContextualDependentCumulativeClosure.MarkedReduct.lam empty pl,
        ContextualDependentCumulativeClosure.MarkedReduct.lam empty pr⟩
  | @base n locals C h as bs T F pieces _ small _ _ read =>
      intro mark localsRigid leftReduct rightReduct
      obtain ⟨sameL, sameR⟩ := read.sides
      have rigidHead := localsRigid h small
      intro piece member
      refine ⟨ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead as leftReduct _ ?_,
        ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead bs rightReduct _ ?_⟩
      · rw [← sameL]
        exact List.mem_map_of_mem member
      · rw [← sameR]
        exact List.mem_map_of_mem member
  | @proj n locals C h first as bs T F pieces _ small _ _ read =>
      intro mark localsRigid leftReduct rightReduct
      obtain ⟨sameL, sameR⟩ := read.sides
      have rigidHead := localsRigid h small
      have leftSpine := ContextualDependentCumulativeClosure.MarkedReduct.of_project empty first
        (ContextualDependentCumulativeClosure.elim_appSpine as (.var h)) leftReduct
      have rightSpine := ContextualDependentCumulativeClosure.MarkedReduct.of_project empty first
        (ContextualDependentCumulativeClosure.elim_appSpine bs (.var h)) rightReduct
      intro piece member
      refine ⟨ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead as leftSpine _ ?_,
        ContextualDependentCumulativeClosure.MarkedReduct.of_spine empty h rigidHead bs rightSpine _ ?_⟩
      · rw [← sameL]
        exact List.mem_map_of_mem member
      · rw [← sameR]
        exact List.mem_map_of_mem member

/-! ## The executable reading, with each instantiated type at the reducer's reduct -/

section Executable

variable (reducer : ExecutableReduction.Reducer S.R)

/-- **The argument pieces of two spines along the reducer's reducts of the instantiated types.** -/
def argPartsN (fuel : Nat) {n : Nat} : Tm Head n → Tm Head n → List (Tm Head n) → List (Tm Head n) →
    Option (List (Piece Head n))
  | .pi DL EL, .pi DR ER, a :: as, b :: bs =>
      (argPartsN fuel (normalCode reducer fuel (inst0 a EL)) (normalCode reducer fuel (inst0 b ER)) as bs).map
        (⟨DL, a, DR, b⟩ :: ·)
  | _, _, [], [] => some []
  | _, _, _, _ => none
termination_by structural _ _ as _ => as

theorem argPartsN_nil (fuel : Nat) {n : Nat} (TL TR : Tm Head n) : argPartsN reducer fuel TL TR [] [] = some [] := by
  cases TL <;> cases TR <;> rfl

theorem argPartsN_nil_cons (fuel : Nat) {n : Nat} (TL TR b : Tm Head n) (bs : List (Tm Head n)) :
    argPartsN reducer fuel TL TR [] (b :: bs) = none := by
  cases TL <;> cases TR <;> rfl

theorem argPartsN_cons_nil (fuel : Nat) {n : Nat} (TL TR a : Tm Head n) (as : List (Tm Head n)) :
    argPartsN reducer fuel TL TR (a :: as) [] = none := by
  cases TL <;> cases TR <;> rfl

/-- **The executable reading is a reading along types that reduce to Π types.** -/
theorem argPartsN_rel (fuel : Nat) {n : Nat} :
    ∀ (as bs : List (Tm Head n)) {TL TR TL₀ TR₀ : Tm Head n} {pieces : List (Piece Head n)},
      argPartsN reducer fuel TL TR as bs = some pieces → Reduces S.R TL₀ TL → Reduces S.R TR₀ TR →
      ∃ F, ArgRel S.R TL₀ TR₀ as bs pieces F
  | [], [], TL, TR, TL₀, TR₀, pieces, found, _, _ => by
      rw [argPartsN_nil] at found
      cases found
      exact ⟨TL₀, .nil _ _⟩
  | [], b :: bs, TL, TR, _, _, _, found, _, _ => by
      rw [argPartsN_nil_cons] at found
      cases found
  | a :: as, [], TL, TR, _, _, _, found, _, _ => by
      rw [argPartsN_cons_nil] at found
      cases found
  | a :: as, b :: bs, TL, TR, TL₀, TR₀, pieces, found, toL, toR => by
      cases TL with
      | pi DL EL =>
          cases TR with
          | pi DR ER =>
              simp only [argPartsN, Option.map_eq_some_iff] at found
              obtain ⟨rest, computed, rfl⟩ := found
              obtain ⟨F, inner⟩ := argPartsN_rel fuel as bs computed (normalCode_reduces reducer fuel _)
                (normalCode_reduces reducer fuel _)
              exact ⟨F, .cons toL toR inner⟩
          | _ => simp [argPartsN] at found
      | _ => simp [argPartsN] at found

/-- The shape of two spines of one local at a rigid base: the local's type and the two argument lists. -/
def baseShape {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (Tm Head n × List (Tm Head n) × List (Tm Head n)) :=
  if rigidBase locals.length C then
    match spineOf left, spineOf right with
    | some (h, as), some (h', bs) =>
        if h = h' ∧ h.val < locals.length ∧ 0 < as.length then (locals[h.val]?).map fun T => (T, as, bs) else none
    | _, _ => none
  else none

theorem baseShape_spec {n : Nat} {locals : List (Tm Head n)} {C left right T : Tm Head n}
    {as bs : List (Tm Head n)} (found : baseShape locals C left right = some (T, as, bs)) :
    ∃ h : Fin n, rigidBase locals.length C = true ∧ left = appSpine (.var h) as ∧
      right = appSpine (.var h) bs ∧ h.val < locals.length ∧ as ≠ [] ∧ locals[h.val]? = some T := by
  unfold baseShape at found
  by_cases base : rigidBase locals.length C = true
  · rw [if_pos base] at found
    cases sl : spineOf left with
    | none => rw [sl] at found; cases found
    | some readL =>
        obtain ⟨h, as'⟩ := readL
        cases sr : spineOf right with
        | none => rw [sl, sr] at found; cases found
        | some readR =>
            obtain ⟨h', bs'⟩ := readR
            rw [sl, sr] at found
            dsimp only at found
            by_cases cond : h = h' ∧ h.val < locals.length ∧ 0 < as'.length
            · rw [if_pos cond] at found
              obtain ⟨rfl, small, positive⟩ := cond
              obtain ⟨T', looked, same⟩ := Option.map_eq_some_iff.mp found
              simp only [Prod.mk.injEq] at same
              obtain ⟨rfl, rfl, rfl⟩ := same
              exact ⟨h, base, spineOf_spec sl, spineOf_spec sr, small, List.length_pos_iff.mp positive, looked⟩
            · rw [if_neg cond] at found
              cases found
  · rw [if_neg base] at found
    cases found

/-- The shape of two equal projections of spines of one local at a rigid base. -/
def projShape {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (Tm Head n × List (Tm Head n) × List (Tm Head n)) :=
  match readProjection left, readProjection right with
  | some (first, l), some (first', r) => if first = first' then baseShape locals C l r else none
  | _, _ => none

theorem projShape_spec {n : Nat} {locals : List (Tm Head n)} {C left right T : Tm Head n}
    {as bs : List (Tm Head n)} (found : projShape locals C left right = some (T, as, bs)) :
    ∃ (first : Bool) (h : Fin n), rigidBase locals.length C = true ∧
      left = project first (appSpine (.var h) as) ∧ right = project first (appSpine (.var h) bs) ∧
      h.val < locals.length ∧ as ≠ [] ∧ locals[h.val]? = some T := by
  unfold projShape at found
  cases rl : readProjection left with
  | none => rw [rl] at found; cases found
  | some readL =>
      obtain ⟨first, l⟩ := readL
      cases rr : readProjection right with
      | none => rw [rl, rr] at found; cases found
      | some readR =>
          obtain ⟨first', r⟩ := readR
          rw [rl, rr] at found
          dsimp only at found
          by_cases same : first = first'
          · rw [if_pos same] at found
            subst same
            obtain ⟨h, base, rfl, rfl, small, nonempty, looked⟩ := baseShape_spec found
            exact ⟨first, h, base, readProjection_spec rl, readProjection_spec rr, small, nonempty, looked⟩
          · rw [if_neg same] at found
            cases found

/-- **Spines of one local, or equal projections of them, at a rigid base, along the reducer's reducts of the
instantiated types.** -/
def dependentBaseN (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    Option (List (Piece Head n)) :=
  ((baseShape locals C left right).bind fun shape => argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2).or
    ((projShape locals C left right).bind fun shape => argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2)

/-- **Dependent spines of one local under abstractions, along the reducer's reducts of the instantiated types.** -/
def dependentUnderN (fuel : Nat) : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n →
    Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (dependentUnderN fuel (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => dependentBaseN reducer fuel locals C left right

theorem dependentUnderN_base (fuel : Nat) {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    (notUnder : ¬ ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r) :
    dependentUnderN reducer fuel locals annotation left right =
      dependentBaseN reducer fuel locals annotation left right := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r => exact absurd ⟨D, T, l, r, rfl, rfl, rfl⟩ notUnder
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- **The executable reading is a reading along types that reduce to Π types.** -/
theorem dependentUnderN_rel (fuel : Nat) {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)} (found : dependentUnderN reducer fuel locals annotation left right = some pieces) :
    DepRel S.R locals annotation left right pieces := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    simp only [dependentUnderN, Option.map_eq_some_iff] at found
    obtain ⟨inner, computed, rfl⟩ := found
    exact .under (dependentUnderN_rel fuel _ T l r computed)
  · rw [dependentUnderN_base reducer fuel view] at found
    unfold dependentBaseN at found
    cases spineRead : (baseShape locals annotation left right).bind fun shape =>
        argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 with
    | some read =>
        rw [spineRead] at found
        cases found
        obtain ⟨⟨T, as, bs⟩, shaped, computed⟩ := Option.bind_eq_some_iff.mp spineRead
        obtain ⟨h, rigidB, rfl, rfl, small, nonempty, looked⟩ := baseShape_spec shaped
        obtain ⟨F, rel⟩ := argPartsN_rel reducer fuel as bs computed .refl .refl
        exact .base rigidB small nonempty looked rel
    | none =>
        rw [spineRead] at found
        obtain ⟨⟨T, as, bs⟩, shaped, computed⟩ := Option.bind_eq_some_iff.mp found
        obtain ⟨first, h, rigidB, rfl, rfl, small, nonempty, looked⟩ := projShape_spec shaped
        obtain ⟨F, rel⟩ := argPartsN_rel reducer fuel as bs computed .refl .refl
        exact .proj rigidB small nonempty looked rel
termination_by sizeOf annotation

/-! ### Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  ContextualDependentConversionBudget.Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem argPartsN_const {n : Nat} :
    ∀ (as bs : List (Tm Head n)) (TL TR : Tm Head n), EventuallyConst fun fuel => argPartsN reducer fuel TL TR as bs
  | [], [], TL, TR => EventuallyConst.of_eq (fun fuel => argPartsN_nil reducer fuel TL TR)
      (EventuallyConst.const _)
  | [], b :: bs, TL, TR => EventuallyConst.of_eq (fun fuel => argPartsN_nil_cons reducer fuel TL TR b bs)
      (EventuallyConst.const _)
  | a :: as, [], TL, TR => EventuallyConst.of_eq (fun fuel => argPartsN_cons_nil reducer fuel TL TR a as)
      (EventuallyConst.const _)
  | a :: as, b :: bs, TL, TR => by
      cases TL with
      | pi DL EL =>
          cases TR with
          | pi DR ER =>
              exact EventuallyConst.dep (h := fun fuel => (normalCode reducer fuel (inst0 a EL),
                  normalCode reducer fuel (inst0 b ER)))
                (k := fun fuel types => (argPartsN reducer fuel types.1 types.2 as bs).map (⟨DL, a, DR, b⟩ :: ·))
                (EventuallyConst.pair (normalCode_const reducer stable _) (normalCode_const reducer stable _))
                (fun types => EventuallyConst.comp _ (argPartsN_const as bs types.1 types.2))
          | _ => exact EventuallyConst.const _
      | _ => exact EventuallyConst.const _

include stable in
theorem dependentBaseN_const {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) :
    EventuallyConst fun fuel => dependentBaseN reducer fuel locals C left right := by
  unfold dependentBaseN
  have spines : EventuallyConst fun fuel => (baseShape locals C left right).bind fun shape =>
      argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 := by
    cases baseShape locals C left right with
    | none => exact EventuallyConst.const _
    | some shape => exact argPartsN_const reducer stable _ _ _ _
  have projections : EventuallyConst fun fuel => (projShape locals C left right).bind fun shape =>
      argPartsN reducer fuel shape.1 shape.1 shape.2.1 shape.2.2 := by
    cases projShape locals C left right with
    | none => exact EventuallyConst.const _
    | some shape => exact argPartsN_const reducer stable _ _ _ _
  exact EventuallyConst.comp (fun pair : Option (List (Piece Head n)) × Option (List (Piece Head n)) =>
    pair.1.or pair.2) (EventuallyConst.pair spines projections)

include stable in
/-- **The executable reading is eventually constant in the budget.** -/
theorem dependentUnderN_const {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => dependentUnderN reducer fuel locals annotation left right := by
  by_cases view : ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r
  · obtain ⟨D, T, l, r, rfl, rfl, rfl⟩ := view
    exact EventuallyConst.comp (Option.map (List.map (Piece.under D))) (dependentUnderN_const _ T l r)
  · exact EventuallyConst.of_eq (fun fuel => dependentUnderN_base reducer fuel view)
      (dependentBaseN_const reducer stable locals annotation left right)
termination_by sizeOf annotation

omit stable in
/-- The executable reading of one equation's sides, with its relational reading. -/
def readArgs (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    Option {pieces : List (Piece Head n) // DepRel S.R [] annotation left right pieces} :=
  match found : dependentUnderN reducer fuel [] annotation left right with
  | some pieces => some ⟨pieces, dependentUnderN_rel reducer fuel [] annotation left right found⟩
  | none => none

omit stable in
theorem readArgs_val (fuel : Nat) {n : Nat} (annotation left right : Tm Head n) :
    (readArgs reducer fuel annotation left right).map Subtype.val =
      dependentUnderN reducer fuel [] annotation left right := by
  unfold readArgs
  split
  · rename_i pieces found
    exact found.symm
  · rename_i found
    exact found.symm

include stable in
theorem readArgs_const {n : Nat} (annotation left right : Tm Head n) :
    EventuallyConst fun fuel => readArgs reducer fuel annotation left right :=
  EventuallyConst.of_injective (g := Option.map Subtype.val) (Option.map_injective Subtype.val_injective)
    (EventuallyConst.of_eq (fun fuel => readArgs_val reducer fuel annotation left right)
      (dependentUnderN_const reducer stable [] annotation left right))

end Executable

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
