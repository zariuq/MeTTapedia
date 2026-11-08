import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyNeutral

/-!
# Neutral spines with dependent heads

The head of a spine may have a **dependent** type `h : (y₁ : D₁) → (y₂ : D₂[y₁]) → ⋯ → E`. The argument
equations are then heterogeneous: `aᵢ : Dᵢ[a₁ … aᵢ₋₁]` against `bᵢ : Dᵢ[b₁ … bᵢ₋₁]`, each at the domain
instantiated at its own earlier arguments. `argParts` reads them along the types of the two spines'
prefixes, which must be literal Π types; the next prefix types instantiate the codomains at the
arguments.

* **Injectivity**: the algorithmic comparison compares the arguments at the left domains
  (`SpineArgs`), and the domains of the two sides are equal once the earlier arguments are
  (`argParts_holds`).
* **Congruence**: application congruence along the left prefix types (`argParts_congr`).
* **Normal forms and weight**: the normal form of the spine is the head applied to the normal forms of
  the arguments, kept at the left prefix types up to typed equality (`along_normal`).

The non-dependent telescopes of `ContextualDependentSpinesManyNeutral` are the special case where
every codomain is a weakening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSpinesMany

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentRigidDecomposition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Reading the argument pieces -/

/-- **The argument pieces of two spines along the types of their prefixes.** -/
def argParts : {n : Nat} → Tm Head n → Tm Head n → List (Tm Head n) → List (Tm Head n) →
    Option (List (Piece Head n))
  | _, .pi DL EL, .pi DR ER, a :: as, b :: bs =>
      (argParts (inst0 a EL) (inst0 b ER) as bs).map (⟨DL, a, DR, b⟩ :: ·)
  | _, _, _, [], [] => some []
  | _, _, _, _, _ => none

theorem argParts_cons_cases {n : Nat} {TL TR a b : Tm Head n} {as bs : List (Tm Head n)}
    {pieces : List (Piece Head n)} (found : argParts TL TR (a :: as) (b :: bs) = some pieces) :
    ∃ DL EL DR ER rest, TL = .pi DL EL ∧ TR = .pi DR ER ∧ argParts (inst0 a EL) (inst0 b ER) as bs = some rest ∧
      pieces = ⟨DL, a, DR, b⟩ :: rest := by
  cases TL with
  | pi DL EL =>
      cases TR with
      | pi DR ER =>
          simp only [argParts, Option.map_eq_some_iff] at found
          obtain ⟨rest, computed, rfl⟩ := found
          exact ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩
      | _ => simp [argParts] at found
  | _ => simp [argParts] at found

theorem argParts_nil_cases {n : Nat} {TL TR : Tm Head n} {bs : List (Tm Head n)} {pieces : List (Piece Head n)}
    (found : argParts TL TR [] bs = some pieces) : bs = [] ∧ pieces = [] := by
  cases bs with
  | nil =>
      cases TL <;> cases TR <;> simp [argParts] at found <;> exact ⟨rfl, found⟩
  | cons b bs => cases TL <;> cases TR <;> simp [argParts] at found

theorem argParts_nil {n : Nat} (TL TR : Tm Head n) : argParts TL TR [] [] = some [] := by
  cases TL <;> cases TR <;> simp [argParts]

theorem argParts_right_nil {n : Nat} {TL TR a : Tm Head n} {as : List (Tm Head n)} {pieces : List (Piece Head n)}
    (found : argParts TL TR (a :: as) [] = some pieces) : False := by
  cases TL <;> cases TR <;> simp [argParts] at found

/-- **The reading is kept by substitution.** -/
theorem argParts_subst {n m : Nat} (σ : Sub Head n m) : ∀ (as bs : List (Tm Head n)) {TL TR : Tm Head n}
    {pieces : List (Piece Head n)}, argParts TL TR as bs = some pieces →
    argParts (Presentation.subst σ TL) (Presentation.subst σ TR) (as.map (Presentation.subst σ))
      (bs.map (Presentation.subst σ)) = some (pieces.map (Piece.subst σ))
  | [], bs, TL, TR, pieces, found => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      exact argParts_nil _ _
  | a :: as, [], _, _, _, found => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, pieces, found => by
      obtain ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      have below := argParts_subst σ as bs computed
      rw [subst_inst0, subst_inst0] at below
      simp only [Presentation.subst, List.map_cons, argParts, below, Option.map_some, Piece.subst]

/-- The type of a spine after its arguments, along literal Π types. -/
def argFinal {n : Nat} : Tm Head n → List (Tm Head n) → Tm Head n
  | .pi _ E, a :: as => argFinal (inst0 a E) as
  | T, _ => T

theorem argFinal_nil {n : Nat} (T : Tm Head n) : argFinal T [] = T := by
  cases T <;> rfl

/-! ## Typing, injectivity and congruence -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts in
/-- **A spine along literal Π types**: when the head's type is below every type of the head, a typed spine
has its arguments at the instantiated domains, and its final type is below the spine's type. -/
theorem argParts_typed_left {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (as bs : List (Tm Head n)) {TL TR f C : Tm Head n} {pieces : List (Piece Head n)},
      argParts TL TR as bs = some pieces →
      (∀ U, TypedEquality.Typed S.R Γ f U → TypeLe S.R Γ TL U) → TypedEquality.Typed S.R Γ f TL →
      TypedEquality.Typed S.R Γ (appSpine f as) C →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) ∧ TypeLe S.R Γ (argFinal TL as) C
  | [], bs, TL, TR, f, C, pieces, found, principal, _, typed => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      refine ⟨fun _ member => by simp at member, ?_⟩
      rw [argFinal_nil]
      exact principal C typed
  | a :: as, [], _, _, _, _, _, found, _, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, f, C, pieces, found, principal, tf, typed => by
      obtain ⟨D, E, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      obtain ⟨U, prefixTyped⟩ := appSpine_prefix_typed (t := .app f a) as typed
      obtain ⟨A, B, tf', ta, _⟩ := Typed.generation prefixTyped
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (principal _ tf') (Typed.isType tf' formed) formed
      have ta' : TypedEquality.Typed S.R Γ a D := Typed.convType ta domains.symm
      have principal' : ∀ U, TypedEquality.Typed S.R Γ (.app f a) U → TypeLe S.R Γ (inst0 a E) U := by
        intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (principal _ tf'') (Typed.isType tf'' formed) formed
        have instantiated : Below S.R Γ (inst0 a E) (inst0 a B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        exact .sub instantiated le'
      obtain ⟨args, final⟩ :=
        argParts_typed_left formed as bs computed principal' (Derivable.appElim tf ta') typed
      refine ⟨fun piece member => ?_, final⟩
      rcases List.mem_cons.mp member with rfl | inner
      · exact ta'
      · exact args piece inner

theorem argParts_swap : ∀ {n : Nat} (as bs : List (Tm Head n)) {TL TR : Tm Head n} {pieces : List (Piece Head n)},
    argParts TL TR as bs = some pieces →
    argParts TR TL bs as = some (pieces.map fun piece => ⟨piece.rightType, piece.right, piece.leftType, piece.left⟩)
  | _, [], bs, TL, TR, pieces, found => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      exact argParts_nil _ _
  | _, a :: as, [], _, _, _, found => (argParts_right_nil found).elim
  | _, a :: as, b :: bs, TL, TR, pieces, found => by
      obtain ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      simp only [argParts, argParts_swap as bs computed, Option.map_some, List.map_cons]

include facts in
/-- **Both spines' arguments are typed at their own domains.** -/
theorem argParts_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (as bs : List (Tm Head n))
    {TL TR f g C : Tm Head n} {pieces : List (Piece Head n)} (found : argParts TL TR as bs = some pieces)
    (principalL : ∀ U, TypedEquality.Typed S.R Γ f U → TypeLe S.R Γ TL U) (tf : TypedEquality.Typed S.R Γ f TL)
    (principalR : ∀ U, TypedEquality.Typed S.R Γ g U → TypeLe S.R Γ TR U) (tg : TypedEquality.Typed S.R Γ g TR)
    (tl : TypedEquality.Typed S.R Γ (appSpine f as) C) (tr : TypedEquality.Typed S.R Γ (appSpine g bs) C) :
    (∀ piece ∈ pieces, piece.Typed S.R Γ) ∧ TypeLe S.R Γ (argFinal TL as) C := by
  obtain ⟨left, final⟩ := argParts_typed_left facts formed as bs found principalL tf tl
  obtain ⟨right, _⟩ := argParts_typed_left facts formed bs as (argParts_swap as bs found) principalR tg tr
  refine ⟨fun piece member => ⟨left piece member, ?_⟩, final⟩
  exact right _ (List.mem_map.mpr ⟨piece, member, rfl⟩)

/-- **Application congruence along the left prefix types.** -/
theorem argParts_congr {n : Nat} {Γ : Ctx Head n} : ∀ (as bs : List (Tm Head n)) {TL TR f g : Tm Head n}
    {pieces : List (Piece Head n)}, argParts TL TR as bs = some pieces →
    (∀ piece ∈ pieces, piece.Holds S.R Γ) → Equal S.R Γ f g TL →
    Equal S.R Γ (appSpine f as) (appSpine g bs) (argFinal TL as)
  | [], bs, TL, TR, f, g, pieces, found, _, same => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      rw [argFinal_nil]
      exact same
  | a :: as, [], _, _, _, _, _, found, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, f, g, pieces, found, held, same => by
      obtain ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      exact argParts_congr as bs computed (fun piece member => held piece (List.mem_cons_of_mem _ member))
        (Derivable.appCong same (held _ List.mem_cons_self).2)

include facts roots heads algebra in
/-- **Along literal Π types, the compared arguments make the pieces hold.** -/
theorem argParts_holds {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (as bs : List (Tm Head n)) {TL TR U : Tm Head n} {pieces : List (Piece Head n)},
      argParts TL TR as bs = some pieces → SpineArgs S Γ TL as bs U → TypeEq S.R Γ TL TR →
      IsType S.R Γ TL → IsType S.R Γ TR → (∀ piece ∈ pieces, piece.Typed S.R Γ) →
      ∀ piece ∈ pieces, piece.Holds S.R Γ
  | [], bs, _, _, _, pieces, found, _, _, _, _, _ => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      simp
  | a :: as, [], _, _, _, _, found, _, _, _, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, U, pieces, found, args, types, isL, isR, typed => by
      obtain ⟨DL, EL, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      cases args with
      | cons red terms others =>
          have same := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape _ _) red.red
          injection same with _ sameA sameB
          have sameA' := sameA.symm
          have sameB' := sameB.symm
          subst sameA'
          subst sameB'
          obtain ⟨ta, tb⟩ := typed _ List.mem_cons_self
          have firsts := Algorithmic.sound_terms facts roots heads algebra formed terms
          obtain ⟨domains, codomains⟩ := (ContextualDependentRigid.typeEq_pi_iff facts formed).mp types
          obtain ⟨_, ⟨v, hv, tEL⟩⟩ := IsType.pi_parts isL
          obtain ⟨_, ⟨v', hv', tER⟩⟩ := IsType.pi_parts isR
          have tER' := Typed.stable tER (CtxEq.snoc (CtxEq.refl Γ formed) domains)
          have nextTypes : TypeEq S.R Γ (inst0 a EL) (inst0 b ER) :=
            TypeEq.trans S.levels (TypeEq.instantiate codomains ta)
              (TypeEq.of_instantiateEq tER' hv' ta firsts)
          have nextL : IsType S.R Γ (inst0 a EL) := ⟨v, hv, Typed.instantiate tEL ta⟩
          have nextR : IsType S.R Γ (inst0 b ER) := ⟨v', hv', Typed.instantiate tER tb⟩
          intro piece member
          rcases List.mem_cons.mp member with rfl | inner
          · exact ⟨domains, firsts⟩
          · exact argParts_holds formed as bs computed others nextTypes nextL nextR
              (fun other member => typed other (List.mem_cons_of_mem _ member)) piece inner

/-! ## Normal forms -/

include facts roots heads algebra rigid complete in
/-- **The normal form of a spine along literal Π types** has the normal forms of the arguments. -/
theorem argParts_normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (as bs : List (Tm Head n)) {TL TR f fn : Tm Head n} {pieces : List (Piece Head n)},
      argParts TL TR as bs = some pieces → Long S.R S.roles (.spine Γ fn TL) → Equal S.R Γ f fn TL →
      (∀ piece ∈ pieces, TypedEquality.Typed S.R Γ piece.left piece.leftType) →
      ∃ (ns : List (Tm Head n)) (ws : List Nat),
        ArgWeights S Γ as (pieces.map (·.leftType)) ws ∧
        Long S.R S.roles (.spine Γ (appSpine fn ns) (argFinal TL as)) ∧
        Equal S.R Γ (appSpine f as) (appSpine fn ns) (argFinal TL as) ∧
        weight (appSpine fn ns) = weight fn + ws.sum + pieces.length
  | [], bs, TL, TR, f, fn, pieces, found, long, same, _ => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      refine ⟨[], [], .nil, ?_, ?_, by simp⟩ <;> rw [argFinal_nil] <;> assumption
  | a :: as, [], _, _, _, _, _, found, _, _, _ => (argParts_right_nil found).elim
  | a :: as, b :: bs, TL, TR, f, fn, pieces, found, long, same, typed => by
      obtain ⟨D, E, DR, ER, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      have ta := typed _ List.mem_cons_self
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      have tPi := Typed.isType long.spine_typed formed
      obtain ⟨_, ⟨v, hv, tE⟩⟩ := IsType.pi_parts tPi
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (inst0 a E)) :=
        .app long (IsType.refl tPi) nA.1 (TypeEq.of_instantiateEq tE hv ta nA.2)
      have applied : Equal S.R Γ (.app f a) (.app fn na) (inst0 a E) := Derivable.appCong same nA.2
      obtain ⟨ns, ws, weights, longRest, equalRest, weighed⟩ := argParts_normal formed as bs computed longApp applied
        (fun piece member => typed piece (List.mem_cons_of_mem _ member))
      refine ⟨na :: ns, weight na :: ws, .cons ⟨na, nA, rfl⟩ weights, longRest, equalRest, ?_⟩
      change weight (appSpine (.app fn na) ns) = _
      rw [weighed]
      simp only [ContextualDependentRank.weight, List.sum_cons, List.length_cons]
      omega

theorem argParts_sides : ∀ {n : Nat} (as bs : List (Tm Head n)) {TL TR : Tm Head n} {pieces : List (Piece Head n)},
    argParts TL TR as bs = some pieces → pieces.map (·.left) = as ∧ pieces.map (·.right) = bs
  | _, [], bs, _, _, _, found => by
      obtain ⟨rfl, rfl⟩ := argParts_nil_cases found
      exact ⟨rfl, rfl⟩
  | _, a :: as, [], _, _, _, found => (argParts_right_nil found).elim
  | _, a :: as, b :: bs, _, _, _, found => by
      obtain ⟨_, _, _, _, rest, rfl, rfl, computed, rfl⟩ := argParts_cons_cases found
      obtain ⟨left, right⟩ := argParts_sides as bs computed
      exact ⟨by simp [left], by simp [right]⟩

theorem ArgWeights.piecesOf {n : Nat} {Γ : Ctx Head n} :
    ∀ {pieces : List (Piece Head n)} {ws ws' : List Nat},
      ArgWeights S Γ (pieces.map (·.left)) (pieces.map (·.leftType)) ws →
      ArgWeights S Γ (pieces.map (·.right)) (pieces.map (·.rightType)) ws' → PiecesWeigh S Γ pieces (ws.sum + ws'.sum)
  | [], [], [], .nil, .nil => rfl
  | piece :: rest, w :: ws, w' :: ws', .cons left others, .cons right others' =>
      ⟨w, w', ws.sum + ws'.sum, left, right, ArgWeights.piecesOf others others', by simp only [List.sum_cons]; omega⟩

include facts roots heads algebra complete in
/-- **Spines of a local of dependent type decompose exactly** at a base type. -/
theorem dependent_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as bs : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T as bs = some pieces) (nonempty : as ≠ []) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) (tr : TypedEquality.Typed S.R Γ (appSpine (.var h) bs) C) :
    Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨typed, final⟩ := argParts_typed facts formed as bs found principal th principal th tl tr
  obtain ⟨sameL, sameR⟩ := argParts_sides as bs found
  have length : as.length = bs.length := by rw [← sameL, ← sameR, List.length_map, List.length_map]
  have isT := Typed.isType th formed
  constructor
  · intro same
    obtain ⟨U, spines⟩ := terms_spine_inv h base nonempty length (complete formed same)
    have args := spines_inv (S := S) h as bs length spines
    rw [headType] at args
    exact argParts_holds facts roots heads algebra formed as bs found args isT.refl isT isT typed
  · intro held
    exact .subEq (argParts_congr as bs found held (.refl th)) (TypeLe.toBelow final (Typed.isType tl formed))

include facts roots heads algebra rigid complete in
/-- **Spines of a local of dependent type weigh more than their argument pieces.** -/
theorem dependent_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as bs : List (Tm Head n)} {T C : Tm Head n} {pieces : List (Piece Head n)} (headType : Ctx.lookup Γ h = T)
    (found : argParts T T as bs = some pieces) (base : BaseType S C)
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
  have side : ∀ {cs ds : List (Tm Head n)} {readPieces : List (Piece Head n)},
      argParts T T cs ds = some readPieces → TypedEquality.Typed S.R Γ (appSpine (.var h) cs) C →
      TypedEquality.Typed S.R Γ (appSpine (.var h) ds) C →
      ∃ ws, ArgWeights S Γ cs (readPieces.map (·.leftType)) ws ∧
        HasWeight S Γ (appSpine (.var h) cs) C (1 + ws.sum + readPieces.length) := by
    intro cs ds readPieces read typedC typedD
    obtain ⟨typed, final⟩ := argParts_typed facts formed cs ds read principal th principal th typedC typedD
    obtain ⟨ns, ws, weights, longSpine, equalSpine, weighed⟩ :=
      argParts_normal facts roots heads algebra rigid complete formed cs ds read longHead (.refl th)
        (fun piece member => (typed piece member).1)
    have below := TypeLe.toBelow final (Typed.isType typedC formed)
    have equalC : Equal S.R Γ (appSpine (.var h) cs) (appSpine (.var h) ns) C := .subEq equalSpine below
    refine ⟨ws, weights, appSpine (.var h) ns,
      ⟨.neutral longSpine below (Equal.typed equalC formed).2 baseC, equalC⟩, ?_⟩
    rw [weighed]
    simp only [ContextualDependentRank.weight]
    try omega
  obtain ⟨sameL, sameR⟩ := argParts_sides as bs found
  obtain ⟨ws, weights, left⟩ := side found tl tr
  obtain ⟨ws', weights', right⟩ := side (argParts_swap as bs found) tr tl
  rw [← sameL] at weights
  rw [List.map_map, ← sameR] at weights'
  have pieces := ArgWeights.piecesOf (S := S) weights (by simpa [Function.comp_def] using weights')
  refine ⟨ws.sum + ws'.sum, _, _, pieces, left, right, ?_⟩
  simp only [List.length_map]
  omega

end Theory

/-! ## Dependent spines under abstractions -/

/-- **The argument pieces of two spines of one local of any Π-telescope type**, under the abstractions
read so far. -/
def dependentBase {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) : Option (List (Piece Head n)) :=
  if rigidBase locals.length C then
    match spineOf left, spineOf right with
    | some (h, as), some (h', bs) =>
        if h = h' ∧ h.val < locals.length ∧ 0 < as.length then
          match locals[h.val]? with
          | some T => argParts T T as bs
          | none => none
        else none
    | _, _ => none
  else none

theorem dependentBase_spec {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : dependentBase locals C left right = some pieces) :
    ∃ h as bs T, rigidBase locals.length C = true ∧ left = appSpine (.var h) as ∧
      right = appSpine (.var h) bs ∧ h.val < locals.length ∧ as ≠ [] ∧ locals[h.val]? = some T ∧
      argParts T T as bs = some pieces := by
  unfold dependentBase at found
  by_cases base : rigidBase locals.length C = true
  · rw [if_pos base] at found
    cases sl : spineOf left with
    | none => rw [sl] at found; cases found
    | some readL =>
        obtain ⟨h, as⟩ := readL
        cases sr : spineOf right with
        | none => rw [sl, sr] at found; cases found
        | some readR =>
            obtain ⟨h', bs⟩ := readR
            rw [sl, sr] at found
            dsimp only at found
            by_cases cond : h = h' ∧ h.val < locals.length ∧ 0 < as.length
            · rw [if_pos cond] at found
              obtain ⟨rfl, small, positive⟩ := cond
              cases looked : locals[h.val]? with
              | none => rw [looked] at found; cases found
              | some T =>
                  rw [looked] at found
                  exact ⟨h, as, bs, T, base, spineOf_spec sl, spineOf_spec sr, small,
                    List.length_pos_iff.mp positive, looked, found⟩
            · rw [if_neg cond] at found
              cases found
  · rw [if_neg base] at found
    cases found

/-- **Dependent spines of one local under abstractions**, read from the annotation and the two sides. -/
def dependentUnder : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n →
    Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (dependentUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => dependentBase locals C left right

theorem dependentUnder_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : dependentUnder locals annotation left right = some pieces) :
    (∃ D T l r inner, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
      dependentUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r = some inner ∧
      pieces = inner.map (Piece.under D)) ∨ dependentBase locals annotation left right = some pieces := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r =>
              simp only [dependentUnder, Option.map_eq_some_iff] at found
              obtain ⟨inner, computed, rfl⟩ := found
              exact .inl ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩
          | _ => exact .inr (by simpa [dependentUnder] using found)
      | _ => exact .inr (by simpa [dependentUnder] using found)
  | _ => exact .inr (by simpa [dependentUnder] using found)

theorem dependentUnder_base {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    (notPi : ∀ D T, C ≠ .pi D T) : dependentUnder locals C left right = dependentBase locals C left right := by
  cases C with
  | pi D T => exact absurd rfl (notPi D T)
  | _ => simp [dependentUnder]

/-- **The reading of dependent spines is kept by substitutions that fix the locals.** -/
theorem dependentUnder_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, dependentUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      dependentUnder (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation)
        (Presentation.subst σ left) (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
  intro n locals annotation left right pieces found m σ fixes bound
  rcases dependentUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have below := dependentUnder_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
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
    simp only [List.map_map] at below
    simp only [Presentation.subst, dependentUnder, List.map_map]
    rw [below]
    simp only [Option.map_some, List.map_map]
    rfl
  · obtain ⟨h, as, bs, T, rigid, rfl, rfl, small, nonempty, looked, read⟩ := dependentBase_spec base
    have hm : h.val < m := by omega
    have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
    rw [dependentUnder_base (rigidBase_not_pi (rigidBase_subst (n := n) fixes bound rigid))]
    unfold dependentBase
    have rigid' : rigidBase (locals.map (Presentation.subst σ)).length (Presentation.subst σ annotation) = true := by
      rw [List.length_map]
      exact rigidBase_subst fixes bound rigid
    rw [if_pos rigid', subst_appSpine, subst_appSpine]
    simp only [Presentation.subst, fixedHead, spineOf_appSpine]
    have cond : True ∧ h.val < (locals.map (Presentation.subst σ)).length ∧
        0 < (as.map (Presentation.subst σ)).length := by
      refine ⟨trivial, by simpa using small, ?_⟩
      rw [List.length_map]
      exact List.length_pos_iff.mpr nonempty
    rw [if_pos cond]
    simp only [List.getElem?_map, looked]
    exact argParts_subst σ as bs read

section UnderTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts in
theorem dependentBase_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : dependentBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) : ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨h, as, bs, T, _, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec found
  have headType := types.head looked
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ T U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) T := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  exact (argParts_typed facts formed as bs read principal th principal th tl tr).1

include facts roots heads algebra complete in
theorem dependentBase_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : dependentBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨h, as, bs, T, base, rfl, rfl, _, nonempty, looked, read⟩ := dependentBase_spec found
  exact dependent_exact facts roots heads algebra complete formed h (types.head looked) read nonempty
    (rigidBase_spec base) tl tr

include facts roots heads algebra rigid complete in
theorem dependentBase_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : dependentBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨h, as, bs, T, base, rfl, rfl, _, _, looked, read⟩ := dependentBase_spec found
  exact dependent_weight facts roots heads algebra rigid complete formed h (types.head looked) read
    (rigidBase_spec base) tl tr

include facts in
/-- **The pieces of dependent spines under abstractions are typed.** -/
theorem dependentUnder_typed : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    dependentUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have below := dependentUnder_typed _ T l r (formed.snoc ⟨u, hu, tD⟩) (types.under D) computed
          (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        intro piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
      · exact dependentBase_typed facts formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact dependentBase_typed facts formed types base tl tr

include facts roots heads algebra complete in
/-- **Dependent spines under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem dependentUnder_exact : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    dependentUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ)
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        have below := dependentUnder_exact _ T l r formedD (types.under D) computed tl' tr'
        have typed := dependentUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
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
      · exact dependentBase_exact facts roots heads algebra complete formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact dependentBase_exact facts roots heads algebra complete formed types base tl tr

include facts roots heads algebra rigid complete in
/-- **Dependent spines under abstractions weigh more than their pieces.** -/
theorem dependentUnder_weight : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    dependentUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 ≤ wl + wr
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
          dependentUnder_weight _ T l r formedD (types.under D) computed tl' tr'
        have typed := dependentUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
        obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
        exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
          HasWeight.under (w := v) hv tPi isD right, total⟩
      · exact dependentBase_weight facts roots heads algebra rigid complete formed types base tl tr
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, tr
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases dependentUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact dependentBase_weight facts roots heads algebra rigid complete formed types base tl tr

end UnderTheory

end ContextualDependentSpinesMany
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
