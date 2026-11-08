import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpinesManyFormers

/-!
# Neutral spines with any number of arguments

R94 decomposed a local applied to two arguments, at a non-dependent binary type. Here the local takes
**any number of arguments** at a non-dependent type `h : D₁ → ⋯ → Dₖ → E`: at a rigid base type,
`h a₁ ⋯ aₖ ≐ h b₁ ⋯ bₖ` has exactly the solutions of the argument equations `aᵢ ≐ bᵢ` at `Dᵢ`.

* **Injectivity.** Completeness gives an algorithmic derivation; at a base type it compares the two
  spines argument by argument (`spines_inv`), along the head's type, which is a literal telescope, so the
  compared domains are the `Dᵢ` themselves (`SpineArgs.telescope`).
* **Congruence.** Application congruence, `k` times, then subsumption to the equation's type.
* **Weight.** The normal form of `h a₁ ⋯ aₖ` at a base type is `h n₁ ⋯ nₖ` for the normal forms `nᵢ` of
  the arguments, so the argument equations weigh `2k + 2` less.

This module gives the readers and the raw theory: `spineOf`, `telescope`, `telescopeOf`, the typing of
spines along a telescope, injectivity, congruence and the normal forms.
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

/-! ## Reading spines and telescopes -/

/-- **The head and arguments of a spine of a variable.** -/
def spineOf : {n : Nat} → Tm Head n → Option (Fin n × List (Tm Head n))
  | _, .var i => some (i, [])
  | _, .app f a => (spineOf f).map fun read => (read.1, read.2 ++ [a])
  | _, .const _ | _, .head _ | _, .pi _ _ | _, .sigma _ _ | _, .id _ _ _ | _, .lam _ | _, .pair _ _
  | _, .fst _ | _, .snd _ | _, .refl _ => none

theorem spineOf_spec : ∀ {n : Nat} {t : Tm Head n} {h : Fin n} {as : List (Tm Head n)},
    spineOf t = some (h, as) → t = appSpine (.var h) as
  | _, .var i, h, as, found => by
      simp only [spineOf, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      rfl
  | _, .app f a, h, as, found => by
      simp only [spineOf, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨⟨h', as'⟩, inner, rfl, rfl⟩ := found
      rw [spineOf_spec inner, appSpine_concat]
  | _, .const _, _, _, found | _, .head _, _, _, found | _, .pi _ _, _, _, found
  | _, .sigma _ _, _, _, found | _, .id _ _ _, _, _, found | _, .lam _, _, _, found
  | _, .pair _ _, _, _, found | _, .fst _, _, _, found | _, .snd _, _, _, found
  | _, .refl _, _, _, found => by simp [spineOf] at found

theorem spineOf_appSpine {n : Nat} (h : Fin n) : ∀ as : List (Tm Head n),
    spineOf (appSpine (.var h) as) = some (h, as) := by
  intro as
  induction as using List.reverseRecOn with
  | nil => rfl
  | append_singleton as a ih =>
      rw [appSpine_concat]
      simp only [spineOf, ih, Option.map_some]

/-- **A non-dependent telescope**: `D₁ → ⋯ → Dₖ → E`, every codomain a weakening. -/
def telescope {n : Nat} : List (Tm Head n) → Tm Head n → Tm Head n
  | [], E => E
  | D :: ds, E => .pi D (Presentation.rename wk (telescope ds E))

theorem subst_telescope {n m : Nat} (σ : Sub Head n m) :
    ∀ (ds : List (Tm Head n)) (E : Tm Head n),
      Presentation.subst σ (telescope ds E) = telescope (ds.map (Presentation.subst σ)) (Presentation.subst σ E)
  | [], E => rfl
  | D :: ds, E => by
      simp only [telescope, Presentation.subst, List.map_cons, subst_liftSub_wk, subst_telescope σ ds E]

/-- Strengthen a code that is a weakening; complete on weakenings. -/
theorem strengthenCode_rename {n : Nat} (code : Tm Head n) :
    (strengthenCode (Presentation.rename wk code)).map Subtype.val = some code := by
  unfold strengthenCode
  have exact := ContextualDependentInversion.lookup_exact (wk : Ren n (n + 1)) (Fin.succ_injective _)
  have inverted := ContextualDependentInversion.invert_rename code wk _ exact
  split
  · rename_i found
    rw [found] at inverted
    cases inverted
  · rename_i strong found
    rw [found] at inverted
    cases inverted
    rfl

/-- **Read a non-dependent telescope of `k` domains** from a type code. -/
def telescopeOf : {n : Nat} → Nat → Tm Head n → Option (List (Tm Head n) × Tm Head n)
  | _, 0, E => some ([], E)
  | _, k + 1, .pi D B => (strengthenCode B).bind fun rest =>
      (telescopeOf k rest.val).map fun read => (D :: read.1, read.2)
  | _, _ + 1, .var _ | _, _ + 1, .const _ | _, _ + 1, .head _ | _, _ + 1, .sigma _ _ | _, _ + 1, .id _ _ _
  | _, _ + 1, .lam _ | _, _ + 1, .app _ _ | _, _ + 1, .pair _ _ | _, _ + 1, .fst _ | _, _ + 1, .snd _
  | _, _ + 1, .refl _ => none

theorem telescopeOf_spec : ∀ {n : Nat} (k : Nat) {T : Tm Head n} {ds : List (Tm Head n)} {E : Tm Head n},
    telescopeOf k T = some (ds, E) → T = telescope ds E ∧ ds.length = k
  | _, 0, T, ds, E, found => by
      simp only [telescopeOf, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨rfl, rfl⟩
  | _, k + 1, .pi D B, ds, E, found => by
      simp only [telescopeOf, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at found
      obtain ⟨⟨rest, same⟩, _, ⟨ds', E'⟩, inner, rfl, rfl⟩ := found
      obtain ⟨shape, length⟩ := telescopeOf_spec k inner
      subst same
      have shape' : rest = telescope ds' E' := shape
      refine ⟨?_, by simp [length]⟩
      simp only [telescope, shape']
  | _, _ + 1, .var _, _, _, found | _, _ + 1, .const _, _, _, found | _, _ + 1, .head _, _, _, found
  | _, _ + 1, .sigma _ _, _, _, found | _, _ + 1, .id _ _ _, _, _, found | _, _ + 1, .lam _, _, _, found
  | _, _ + 1, .app _ _, _, _, found | _, _ + 1, .pair _ _, _, _, found | _, _ + 1, .fst _, _, _, found
  | _, _ + 1, .snd _, _, _, found | _, _ + 1, .refl _, _, _, found => by simp [telescopeOf] at found

theorem telescopeOf_telescope {n : Nat} : ∀ (ds : List (Tm Head n)) (E : Tm Head n),
    telescopeOf ds.length (telescope ds E) = some (ds, E)
  | [], E => rfl
  | D :: ds, E => by
      have strong := strengthenCode_rename (telescope ds E)
      obtain ⟨rest, found, same⟩ := Option.map_eq_some_iff.mp strong
      simp only [List.length_cons, telescope, telescopeOf, found, Option.bind_some, same,
        telescopeOf_telescope ds E, Option.map_some]

/-- The weight of a spine. -/
theorem weight_appSpine {n : Nat} : ∀ (f : Tm Head n) (as : List (Tm Head n)),
    weight (appSpine f as) = weight f + (as.map fun a => weight a + 1).sum
  | f, [] => by simp
  | f, a :: as => by
      have := weight_appSpine (.app f a) as
      simp only [appSpine, List.foldl_cons] at this ⊢
      rw [this]
      simp only [ContextualDependentRank.weight, List.map_cons, List.sum_cons]
      omega

/-! ## The pieces of two spines -/

/-- The argument equations of two spines along the domains of a telescope. -/
def spinePieces {n : Nat} : List (Tm Head n) → List (Tm Head n) → List (Tm Head n) → List (Piece Head n)
  | D :: ds, a :: as, b :: bs => ⟨D, a, D, b⟩ :: spinePieces ds as bs
  | _, _, _ => []

theorem spinePieces_subst {n m : Nat} (σ : Sub Head n m) : ∀ (ds as bs : List (Tm Head n)),
    (spinePieces ds as bs).map (Piece.subst σ) =
      spinePieces (ds.map (Presentation.subst σ)) (as.map (Presentation.subst σ)) (bs.map (Presentation.subst σ))
  | D :: ds, a :: as, b :: bs => by
      simp only [spinePieces, List.map_cons, Piece.subst, spinePieces_subst σ ds as bs]
  | [], _, _ => by simp [spinePieces]
  | _ :: _, [], _ => by simp [spinePieces]
  | _ :: _, _ :: _, [] => by simp [spinePieces]

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- A spine's head is typed when the spine is. -/
theorem appSpine_prefix_typed {n : Nat} {Γ : Ctx Head n} : ∀ (as : List (Tm Head n)) {t C : Tm Head n},
    TypedEquality.Typed S.R Γ (appSpine t as) C → ∃ U, TypedEquality.Typed S.R Γ t U
  | [], _, C, typed => ⟨C, typed⟩
  | a :: as, t, C, typed => by
      obtain ⟨U, prefixTyped⟩ := appSpine_prefix_typed (t := .app t a) as typed
      obtain ⟨A, B, tt, _, _⟩ := Typed.generation prefixTyped
      exact ⟨_, tt⟩

include facts in
/-- **A spine along a telescope**: when the head's type is below every type of the head, a typed spine
has its arguments at the domains, and the final codomain is below the spine's type. -/
theorem spine_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (ds as : List (Tm Head n)) (E : Tm Head n) {f C : Tm Head n}, as.length = ds.length →
      (∀ U, TypedEquality.Typed S.R Γ f U → TypeLe S.R Γ (telescope ds E) U) →
      TypedEquality.Typed S.R Γ f (telescope ds E) → TypedEquality.Typed S.R Γ (appSpine f as) C →
      List.Forall₂ (TypedEquality.Typed S.R Γ) as ds ∧ TypeLe S.R Γ E C
  | [], [], E, f, C, _, principal, _, typed => ⟨.nil, principal C typed⟩
  | D :: ds, a :: as, E, f, C, length, principal, tf, typed => by
      obtain ⟨U, prefixTyped⟩ := appSpine_prefix_typed (t := .app f a) as typed
      obtain ⟨A, B, tf', ta, _⟩ := Typed.generation prefixTyped
      obtain ⟨domains, _⟩ := TypeLe.pi_parts facts (principal _ tf') (Typed.isType tf' formed) formed
      have ta' : TypedEquality.Typed S.R Γ a D := Typed.convType ta domains.symm
      have principal' : ∀ U, TypedEquality.Typed S.R Γ (.app f a) U → TypeLe S.R Γ (telescope ds E) U := by
        intro U typedU
        obtain ⟨A', B', tf'', ta'', le'⟩ := Typed.generation typedU
        obtain ⟨doms, codoms⟩ := TypeLe.pi_parts facts (principal _ tf'') (Typed.isType tf'' formed) formed
        have instantiated : Below S.R Γ (inst0 a (Presentation.rename wk (telescope ds E))) (inst0 a B') :=
          Derivable.substitutes codoms (SubstMor.single (Typed.convType ta'' doms.symm))
        rw [inst0_rename_wk] at instantiated
        exact .sub instantiated le'
      have tfa : TypedEquality.Typed S.R Γ (.app f a) (telescope ds E) := by
        have applied := Derivable.appElim tf ta'
        rw [inst0_rename_wk] at applied
        exact applied
      obtain ⟨args, final⟩ := spine_typed formed ds as E (by simpa using length) principal' tfa typed
      exact ⟨.cons ta' args, final⟩
  | [], _ :: _, _, _, _, length, _, _, _ => by simp at length
  | _ :: _, [], _, _, _, length, _, _, _ => by simp at length

/-- **Application congruence along a telescope.** -/
theorem spine_congr {n : Nat} {Γ : Ctx Head n} :
    ∀ (ds as bs : List (Tm Head n)) (E : Tm Head n) {f g : Tm Head n}, as.length = ds.length →
      bs.length = ds.length → (∀ piece ∈ spinePieces ds as bs, piece.Holds S.R Γ) →
      Equal S.R Γ f g (telescope ds E) → Equal S.R Γ (appSpine f as) (appSpine g bs) E
  | [], [], [], _, _, _, _, _, _, same => same
  | D :: ds, a :: as, b :: bs, E, f, g, la, lb, held, same => by
      have applied := Derivable.appCong same (held _ List.mem_cons_self).2
      rw [inst0_rename_wk] at applied
      exact spine_congr ds as bs E (by simpa using la) (by simpa using lb)
        (fun piece member => held piece (List.mem_cons_of_mem _ member)) applied
  | [], _ :: _, _, _, _, _, la, _, _, _ => by simp at la
  | [], [], _ :: _, _, _, _, _, lb, _, _ => by simp at lb
  | _ :: _, [], _, _, _, _, la, _, _, _ => by simp at la
  | _ :: _, _ :: _, [], _, _, _, _, lb, _, _ => by simp at lb

/-! ### Injectivity -/

/-- **Argument comparisons along a spine**, read from the head outward. -/
inductive SpineArgs (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) :
    Tm Head n → List (Tm Head n) → List (Tm Head n) → Tm Head n → Prop
  | nil {T : Tm Head n} : SpineArgs S Γ T [] [] T
  | cons {T A a b U : Tm Head n} {B : Tm Head (n + 1)} {as bs : List (Tm Head n)} :
      RedTy S.R S.roles Γ T (.pi A B) → Algorithmic S.R S.roles (.terms Γ a b A) →
      SpineArgs S Γ (inst0 a B) as bs U → SpineArgs S Γ T (a :: as) (b :: bs) U

theorem SpineArgs.snoc {n : Nat} {Γ : Ctx Head n} {T U A a b : Tm Head n} {B : Tm Head (n + 1)}
    {as bs : List (Tm Head n)} (args : SpineArgs S Γ T as bs U) (red : RedTy S.R S.roles Γ U (.pi A B))
    (terms : Algorithmic S.R S.roles (.terms Γ a b A)) :
    SpineArgs S Γ T (as ++ [a]) (bs ++ [b]) (inst0 a B) := by
  induction args with
  | nil => exact .cons red terms .nil
  | cons r t _ ih => exact .cons r t (ih red)

/-- **The algorithmic comparison of two spines of a variable**, argument by argument. -/
theorem spines_inv {n : Nat} {Γ : Ctx Head n} (h : Fin n) : ∀ (as bs : List (Tm Head n)) {U : Tm Head n},
    as.length = bs.length →
    Algorithmic S.R S.roles (.spines Γ (appSpine (.var h) as) (appSpine (.var h) bs) U) →
    SpineArgs S Γ (Ctx.lookup Γ h) as bs U := by
  intro as
  induction as using List.reverseRecOn with
  | nil =>
      intro bs U length derivation
      cases bs with
      | nil =>
          cases derivation
          exact .nil
      | cons => simp at length
  | append_singleton as a ih =>
      intro bs U length derivation
      rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
      · simp at length
      · rw [List.concat_eq_append] at length derivation ⊢
        rw [appSpine_concat, appSpine_concat] at derivation
        cases derivation with
        | app inner terms =>
            cases inner with
            | spinesW prefixSpines red _ =>
                exact (ih bs' (by simpa using length) prefixSpines).snoc red terms

theorem neutral_appSpine {n : Nat} (h : Fin n) : ∀ as : List (Tm Head n), Neutral S.roles (appSpine (.var h) as) := by
  intro as
  induction as using List.reverseRecOn with
  | nil => exact .var h
  | append_singleton as a ih =>
      rw [appSpine_concat]
      exact .app ih

/-- **At a base type, the algorithmic comparison of two spines compares their spines.** -/
theorem terms_spine_inv {n : Nat} {Γ : Ctx Head n} (h : Fin n) {as bs : List (Tm Head n)} {C : Tm Head n}
    (base : BaseType S C) (nonempty : as ≠ []) (length : as.length = bs.length)
    (derivation : Algorithmic S.R S.roles (.terms Γ (appSpine (.var h) as) (appSpine (.var h) bs) C)) :
    ∃ U, Algorithmic S.R S.roles (.spines Γ (appSpine (.var h) as) (appSpine (.var h) bs) U) := by
  obtain ⟨as', a, rfl⟩ := List.eq_nil_or_concat as |>.resolve_left nonempty
  rcases List.eq_nil_or_concat bs with rfl | ⟨bs', b, rfl⟩
  · simp at length
  rw [List.concat_eq_append, List.concat_eq_append, appSpine_concat, appSpine_concat] at derivation ⊢
  have leftNeutral : Neutral S.roles (.app (appSpine (.var h) as') a) := .app (neutral_appSpine h as')
  have rightNeutral : Neutral S.roles (.app (appSpine (.var h) bs') b) := .app (neutral_appSpine h bs')
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
      have typeSame := WhRed.eq_of_whnf (S := S) base.whnf typeRed.red
      have leftSame := WhRed.eq_of_whnf (S := S) (leftNeutral.whnf S.shape) leftRed.red
      have rightSame := WhRed.eq_of_whnf (S := S) (rightNeutral.whnf S.shape) rightRed.red
      subst typeSame
      subst leftSame
      subst rightSame
      cases inner with
      | univ _ _ _ types =>
          cases types with
          | neutralTypes _ _ _ spines =>
              cases spines with
              | spinesW inner _ _ => exact ⟨_, inner⟩
      | eta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.1 _ _)
      | sigmaEta =>
          rcases base with ⟨_, _, _, impossible⟩ | ⟨_, impossible⟩ | neutral
          · cases impossible
          · cases impossible
          · exact absurd rfl (neutral.not_former.2.2.1 _ _)
      | spine _ _ _ _ _ spines =>
          cases spines with
          | spinesW inner _ _ => exact ⟨_, inner⟩

include facts roots heads algebra in
/-- **Along a telescope, the compared arguments are equal at the domains.** -/
theorem SpineArgs.telescope_holds {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (ds as bs : List (Tm Head n)) (E : Tm Head n) {U : Tm Head n},
      SpineArgs S Γ (telescope ds E) as bs U → List.Forall₂ (TypedEquality.Typed S.R Γ) as ds →
      ∀ piece ∈ spinePieces ds as bs, piece.Holds S.R Γ
  | D :: ds, a :: as, b :: bs, E, U, args, typed => by
      cases args with
      | cons red terms rest =>
          have same := WhRed.eq_of_whnf (S := S) (pi_whnf S.shape _ _) red.red
          change Tm.pi _ _ = Tm.pi D (Presentation.rename wk (telescope ds E)) at same
          injection same with _ sameA sameB
          subst sameA
          subst sameB
          rw [inst0_rename_wk] at rest
          cases typed with
          | cons ta others =>
              intro piece member
              rcases List.mem_cons.mp member with rfl | inner
              · exact ⟨(Typed.isType ta formed).refl, Algorithmic.sound_terms facts roots heads algebra formed terms⟩
              · exact SpineArgs.telescope_holds formed ds as bs E rest others piece inner
  | [], _, _, _, _, _, _ => by simp [spinePieces]
  | _ :: _, [], _, _, _, _, _ => by simp [spinePieces]
  | _ :: _, _ :: _, [], _, _, args, _ => by cases args

include facts in
/-- A base type is not a Π or Σ type. -/
theorem BaseType.base {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {C : Tm Head n}
    (base : BaseType S C) : Base S.R Γ C := by
  have form : IsTypeForm S.roles C := by
    rcases base with ⟨X, a, b, rfl⟩ | ⟨u, rfl⟩ | neutral
    · exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))
    · exact .inl ⟨_, rfl⟩
    · exact .inr (.inr (.inr (.inr (.inl neutral))))
  constructor
  · intro A B equal
    obtain ⟨_, _, same, _⟩ := (facts.forms equal.symm formed (.inr (.inl ⟨_, _, rfl⟩)) form).pi_left
    rcases base with ⟨X, a, b, rfl⟩ | ⟨u, rfl⟩ | neutral
    · cases same
    · cases same
    · exact neutral.not_former.2.1 _ _ same
  · intro A B equal
    obtain ⟨_, _, same, _⟩ := (facts.forms equal.symm formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) form).sigma_left
    rcases base with ⟨X, a, b, rfl⟩ | ⟨u, rfl⟩ | neutral
    · cases same
    · cases same
    · exact neutral.not_former.2.2.1 _ _ same

include facts roots heads algebra complete in
/-- **Spines of a local of a non-dependent type decompose exactly** at a base type. -/
theorem spine_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {ds as bs : List (Tm Head n)} {E C : Tm Head n} (headType : Ctx.lookup Γ h = telescope ds E)
    (la : as.length = ds.length) (lb : bs.length = ds.length) (nonempty : ds ≠ []) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) :
    Equal S.R Γ (appSpine (.var h) as) (appSpine (.var h) bs) C ↔ ∀ piece ∈ spinePieces ds as bs, piece.Holds S.R Γ := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (telescope ds E) U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) (telescope ds E) := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  obtain ⟨argsTyped, final⟩ := spine_typed facts formed ds as E la principal th tl
  have asNonempty : as ≠ [] := by
    intro empty
    rw [empty] at la
    exact nonempty (List.length_eq_zero_iff.mp la.symm)
  constructor
  · intro same
    obtain ⟨U, spines⟩ := terms_spine_inv h base asNonempty (la.trans lb.symm) (complete formed same)
    have args := spines_inv (S := S) h as bs (la.trans lb.symm) spines
    rw [headType] at args
    exact SpineArgs.telescope_holds facts roots heads algebra formed ds as bs E args argsTyped
  · intro held
    have inner := spine_congr ds as bs E la lb held (.refl th)
    exact .subEq inner (TypeLe.toBelow final (Typed.isType tl formed))

/-! ### Weights -/

/-- Argument normal forms of the given weights. -/
inductive ArgWeights (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) :
    List (Tm Head n) → List (Tm Head n) → List Nat → Prop
  | nil : ArgWeights S Γ [] [] []
  | cons {a D : Tm Head n} {w : Nat} {as ds : List (Tm Head n)} {ws : List Nat} :
      HasWeight S Γ a D w → ArgWeights S Γ as ds ws → ArgWeights S Γ (a :: as) (D :: ds) (w :: ws)

theorem ArgWeights.pieces {n : Nat} {Γ : Ctx Head n} {as bs ds : List (Tm Head n)} {ws ws' : List Nat}
    (left : ArgWeights S Γ as ds ws) (right : ArgWeights S Γ bs ds ws') :
    PiecesWeigh S Γ (spinePieces ds as bs) (ws.sum + ws'.sum) := by
  induction left generalizing bs ws' with
  | nil =>
      cases right
      rfl
  | cons weighs _ ih =>
      cases right with
      | cons weighs' others' =>
          exact ⟨_, _, _, weighs, weighs', ih others', by simp only [List.sum_cons]; omega⟩

include facts roots heads algebra rigid complete in
/-- **The normal form of a spine along a telescope** has the normal forms of the arguments. -/
theorem spine_normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) :
    ∀ (ds as : List (Tm Head n)) (E : Tm Head n) {f fn : Tm Head n},
      Long S.R S.roles (.spine Γ fn (telescope ds E)) → Equal S.R Γ f fn (telescope ds E) →
      List.Forall₂ (TypedEquality.Typed S.R Γ) as ds →
      ∃ (ns : List (Tm Head n)) (ws : List Nat), ArgWeights S Γ as ds ws ∧
        Long S.R S.roles (.spine Γ (appSpine fn ns) E) ∧ Equal S.R Γ (appSpine f as) (appSpine fn ns) E ∧
        weight (appSpine fn ns) = weight fn + ws.sum + ds.length
  | [], [], E, f, fn, long, same, _ => ⟨[], [], .nil, long, same, by simp⟩
  | D :: ds, a :: as, E, f, fn, long, same, .cons ta others => by
      obtain ⟨na, nA⟩ := long_exists facts roots heads algebra rigid complete formed ta
      have tPi := Typed.isType long.spine_typed formed
      have longApp : Long S.R S.roles (.spine Γ (.app fn na) (telescope ds E)) := by
        refine .app long (IsType.refl tPi) nA.1 ?_
        rw [inst0_rename_wk]
        have tRest := Typed.isType (Derivable.appElim long.spine_typed nA.1.typed) formed
        rw [inst0_rename_wk] at tRest
        exact IsType.refl tRest
      have applied := Derivable.appCong same nA.2
      rw [inst0_rename_wk] at applied
      obtain ⟨ns, ws, weights, longRest, equalRest, weighed⟩ := spine_normal formed ds as E longApp applied others
      refine ⟨na :: ns, weight na :: ws, .cons ⟨na, nA, rfl⟩ weights, longRest, equalRest, ?_⟩
      change weight (appSpine (.app fn na) ns) = _
      rw [weighed]
      simp only [ContextualDependentRank.weight, List.sum_cons, List.length_cons]
      omega

include facts roots heads algebra rigid complete in
/-- **Spines weigh more than their argument pieces**, by `2k + 2`. -/
theorem spine_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {ds as bs : List (Tm Head n)} {E C : Tm Head n} (headType : Ctx.lookup Γ h = telescope ds E)
    (la : as.length = ds.length) (lb : bs.length = ds.length) (base : BaseType S C)
    (tl : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C)
    (tr : TypedEquality.Typed S.R Γ (appSpine (.var h) bs) C) :
    ∃ w wl wr, PiecesWeigh S Γ (spinePieces ds as bs) w ∧ HasWeight S Γ (appSpine (.var h) as) C wl ∧
      HasWeight S Γ (appSpine (.var h) bs) C wr ∧ w + 2 ≤ wl + wr := by
  have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (telescope ds E) U := by
    intro U typed
    have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  have th : TypedEquality.Typed S.R Γ (.var h) (telescope ds E) := by
    have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed
  have longHead : Long S.R S.roles (.spine Γ (.var h) (telescope ds E)) := by
    refine .var h ?_
    rw [headType]
    exact IsType.refl (Typed.isType th formed)
  have baseC := BaseType.base facts formed base
  have side : ∀ {cs : List (Tm Head n)}, cs.length = ds.length →
      TypedEquality.Typed S.R Γ (appSpine (.var h) cs) C →
      ∃ ws, ArgWeights S Γ cs ds ws ∧ HasWeight S Γ (appSpine (.var h) cs) C (1 + ws.sum + ds.length) := by
    intro cs length typed
    obtain ⟨argsTyped, final⟩ := spine_typed facts formed ds cs E length principal th typed
    obtain ⟨ns, ws, weights, longSpine, equalSpine, weighed⟩ :=
      spine_normal facts roots heads algebra rigid complete formed ds cs E longHead (.refl th) argsTyped
    have below := TypeLe.toBelow final (Typed.isType typed formed)
    have equalC : Equal S.R Γ (appSpine (.var h) cs) (appSpine (.var h) ns) C := .subEq equalSpine below
    refine ⟨ws, weights, appSpine (.var h) ns,
      ⟨.neutral longSpine below (Equal.typed equalC formed).2 baseC, equalC⟩, ?_⟩
    rw [weighed]
    simp only [ContextualDependentRank.weight]
    try omega
  obtain ⟨ws, weights, left⟩ := side la tl
  obtain ⟨ws', weights', right⟩ := side lb tr
  exact ⟨ws.sum + ws'.sum, _, _, ArgWeights.pieces weights weights', left, right, by omega⟩

end Theory

/-! ## Spines under abstractions -/

/-- **The types of the locals read so far**: the `j`-th entry is the type of the variable `j`. -/
def LocalTypes {n : Nat} (Γ : Ctx Head n) (locals : List (Tm Head n)) : Prop :=
  ∀ (j : Nat) (T : Tm Head n), locals[j]? = some T → ∃ hj : j < n, Ctx.lookup Γ ⟨j, hj⟩ = T

theorem LocalTypes.nil {n : Nat} (Γ : Ctx Head n) : LocalTypes Γ ([] : List (Tm Head n)) :=
  fun _ _ found => by simp at found

theorem LocalTypes.under {n : Nat} {Γ : Ctx Head n} {locals : List (Tm Head n)} (D : Tm Head n)
    (types : LocalTypes Γ locals) :
    LocalTypes (.snoc Γ D) (Presentation.rename wk D :: locals.map (Presentation.rename wk)) := by
  intro j T found
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      exact ⟨Nat.zero_lt_succ _, by rw [← found]; rfl⟩
  | succ j =>
      simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at found
      obtain ⟨T', inner, rfl⟩ := found
      obtain ⟨hj, same⟩ := types j T' inner
      exact ⟨Nat.succ_lt_succ hj, by rw [← same]; rfl⟩

/-- **A substitution fixes the first `k` variables.** -/
def Fixes {n m : Nat} (σ : Sub Head n m) (k : Nat) : Prop :=
  ∀ (j : Nat) (hn : j < n) (hm : j < m), j < k → σ ⟨j, hn⟩ = .var ⟨j, hm⟩

theorem Fixes.lift {n m : Nat} {σ : Sub Head n m} {k : Nat} (fixes : Fixes σ k) : Fixes (liftSub σ) (k + 1) := by
  intro j hn hm hk
  cases j with
  | zero => rfl
  | succ j =>
      change Presentation.rename wk (σ ⟨j, by omega⟩) = _
      rw [fixes j (by omega) (by omega) (by omega)]
      rfl

/-- The rigid base types under the abstractions read so far: universes, identity types, locals. -/
def rigidBase {n : Nat} (depth : Nat) : Tm Head n → Bool
  | .head _ => true
  | .id _ _ _ => true
  | .var j => decide (j.val < depth)
  | .const _ | .pi _ _ | .sigma _ _ | .lam _ | .app _ _ | .pair _ _ | .fst _ | .snd _ | .refl _ => false

theorem rigidBase_spec {n : Nat} {depth : Nat} {C : Tm Head n} (base : rigidBase depth C = true) :
    BaseType S C := by
  cases C with
  | head u => exact .inr (.inl ⟨u, rfl⟩)
  | id X a b => exact .inl ⟨X, a, b, rfl⟩
  | var j => exact .inr (.inr (.var j))
  | _ => simp [rigidBase] at base

theorem rigidBase_not_pi {n : Nat} {depth : Nat} {C : Tm Head n} (base : rigidBase depth C = true) :
    ∀ D T, C ≠ .pi D T := by
  intro D T same
  subst same
  simp [rigidBase] at base

theorem rigidBase_subst {n m : Nat} {depth : Nat} {σ : Sub Head n m} (fixes : Fixes σ depth) (bound : depth ≤ m)
    {C : Tm Head n} (base : rigidBase depth C = true) : rigidBase depth (Presentation.subst σ C) = true := by
  cases C with
  | head u => rfl
  | id X a b => rfl
  | var j =>
      have small : j.val < depth := by simpa [rigidBase] using base
      change rigidBase depth (σ j) = true
      rw [show j = ⟨j.val, j.isLt⟩ from rfl, fixes j.val j.isLt (by omega) small]
      simpa [rigidBase] using small
  | _ => simp [rigidBase] at base

/-- **The argument pieces of two spines of one local**, under the abstractions read so far. -/
def spineBase {n : Nat} (locals : List (Tm Head n)) (C left right : Tm Head n) : Option (List (Piece Head n)) :=
  if rigidBase locals.length C then
    match spineOf left, spineOf right with
    | some (h, as), some (h', bs) =>
        if h = h' ∧ h.val < locals.length ∧ as.length = bs.length ∧ 0 < as.length then
          match locals[h.val]? with
          | some T => (telescopeOf as.length T).map fun read => spinePieces read.1 as bs
          | none => none
        else none
    | _, _ => none
  else none

theorem spineBase_spec {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : spineBase locals C left right = some pieces) :
    ∃ h as bs ds E, rigidBase locals.length C = true ∧ left = appSpine (.var h) as ∧
      right = appSpine (.var h) bs ∧ h.val < locals.length ∧ as.length = ds.length ∧ bs.length = ds.length ∧
      ds ≠ [] ∧ locals[h.val]? = some (telescope ds E) ∧ pieces = spinePieces ds as bs := by
  unfold spineBase at found
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
            by_cases cond : h = h' ∧ h.val < locals.length ∧ as.length = bs.length ∧ 0 < as.length
            · rw [if_pos cond] at found
              obtain ⟨rfl, small, length, positive⟩ := cond
              cases looked : locals[h.val]? with
              | none => rw [looked] at found; cases found
              | some T =>
                  rw [looked] at found
                  dsimp only at found
                  obtain ⟨⟨ds, E⟩, read, rfl⟩ := Option.map_eq_some_iff.mp found
                  obtain ⟨shape, dlength⟩ := telescopeOf_spec _ read
                  subst shape
                  refine ⟨h, as, bs, ds, E, base, spineOf_spec sl, spineOf_spec sr, small, dlength.symm,
                    length.symm.trans dlength.symm, ?_, looked, rfl⟩
                  intro empty
                  rw [empty] at dlength
                  simp at dlength
                  omega
            · rw [if_neg cond] at found
              cases found
  · rw [if_neg base] at found
    cases found

/-- **Spines of one local under abstractions**, read from the annotation and the two sides; no budget. -/
def spineUnder : {n : Nat} → List (Tm Head n) → Tm Head n → Tm Head n → Tm Head n → Option (List (Piece Head n))
  | _, locals, .pi D T, .lam left, .lam right =>
      (spineUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T left right).map
        (List.map (Piece.under D))
  | _, locals, C, left, right => spineBase locals C left right

theorem spineUnder_cases {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (found : spineUnder locals annotation left right = some pieces) :
    (∃ D T l r inner, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r ∧
      spineUnder (Presentation.rename wk D :: locals.map (Presentation.rename wk)) T l r = some inner ∧
      pieces = inner.map (Piece.under D)) ∨ spineBase locals annotation left right = some pieces := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r =>
              simp only [spineUnder, Option.map_eq_some_iff] at found
              obtain ⟨inner, computed, rfl⟩ := found
              exact .inl ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩
          | _ => exact .inr (by simpa [spineUnder] using found)
      | _ => exact .inr (by simpa [spineUnder] using found)
  | _ => exact .inr (by simpa [spineUnder] using found)

theorem spineUnder_base {n : Nat} {locals : List (Tm Head n)} {C left right : Tm Head n}
    (notPi : ∀ D T, C ≠ .pi D T) : spineUnder locals C left right = spineBase locals C left right := by
  cases C with
  | pi D T => exact absurd rfl (notPi D T)
  | _ => simp [spineUnder]

/-- **The reading of spines is kept by substitutions that fix the locals.** -/
theorem spineUnder_subst : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {pieces : List (Piece Head n)}, spineUnder locals annotation left right = some pieces →
    ∀ {m : Nat} (σ : Sub Head n m), Fixes σ locals.length → locals.length ≤ m →
      spineUnder (locals.map (Presentation.subst σ)) (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) = some (pieces.map (Piece.subst σ)) := by
  intro n locals annotation left right pieces found m σ fixes bound
  rcases spineUnder_cases found with ⟨D, T, l, r, inner, rfl, rfl, rfl, computed, rfl⟩ | base
  · have below := spineUnder_subst _ T l r computed (liftSub σ) (by simpa using fixes.lift) (by simp; omega)
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
    simp only [Presentation.subst, spineUnder, List.map_map]
    rw [below]
    simp only [Option.map_some, List.map_map]
    rfl
  · obtain ⟨h, as, bs, ds, E, rigid, rfl, rfl, small, la, lb, nonempty, looked, rfl⟩ := spineBase_spec base
    have hm : h.val < m := by omega
    have fixedHead : σ h = .var ⟨h.val, hm⟩ := fixes h.val h.isLt hm small
    have notPi := rigidBase_not_pi (rigidBase_subst (n := n) fixes bound rigid)
    rw [spineUnder_base notPi]
    unfold spineBase
    have rigid' : rigidBase (locals.map (Presentation.subst σ)).length (Presentation.subst σ annotation) = true := by
      rw [List.length_map]
      exact rigidBase_subst fixes bound rigid
    rw [if_pos rigid', subst_appSpine, subst_appSpine]
    simp only [Presentation.subst, fixedHead, spineOf_appSpine]
    have cond : (⟨h.val, hm⟩ : Fin m) = ⟨h.val, hm⟩ ∧ h.val < (locals.map (Presentation.subst σ)).length ∧
        (as.map (Presentation.subst σ)).length = (bs.map (Presentation.subst σ)).length ∧
        0 < (as.map (Presentation.subst σ)).length := by
      refine ⟨rfl, by simpa using small, by simp [la, lb], ?_⟩
      rw [List.length_map, la]
      exact List.length_pos_iff.mpr nonempty
    rw [if_pos ⟨trivial, cond.2⟩]
    simp only [List.getElem?_map, looked, Option.map_some, subst_telescope]
    have read := telescopeOf_telescope (ds.map (Presentation.subst σ)) (Presentation.subst σ E)
    rw [List.length_map] at read
    rw [List.length_map, la, read, Option.map_some, spinePieces_subst]

/-! ### Typing, exactness and weight of the reading -/

section UnderTheory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

theorem spinePieces_typed {n : Nat} {Γ : Ctx Head n} :
    ∀ {ds as bs : List (Tm Head n)}, List.Forall₂ (TypedEquality.Typed S.R Γ) as ds →
      List.Forall₂ (TypedEquality.Typed S.R Γ) bs ds → ∀ piece ∈ spinePieces ds as bs, piece.Typed S.R Γ
  | [], [], [], .nil, .nil => by simp [spinePieces]
  | D :: ds, a :: as, b :: bs, .cons ta others, .cons tb others' => by
      intro piece member
      rcases List.mem_cons.mp member with rfl | inner
      · exact ⟨ta, tb⟩
      · exact spinePieces_typed others others' piece inner

/-- The head of a spine along its declared telescope. -/
theorem head_principal {n : Nat} {Γ : Ctx Head n} {h : Fin n} {ds : List (Tm Head n)} {E : Tm Head n}
    (headType : Ctx.lookup Γ h = telescope ds E) :
    (∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (telescope ds E) U) ∧
      TypedEquality.Typed S.R Γ (.var h) (telescope ds E) := by
  refine ⟨fun U typed => ?_, ?_⟩
  · have le : TypeLe S.R Γ (Ctx.lookup Γ h) U := Typed.generation typed
    rwa [headType] at le
  · have typed : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
    rwa [headType] at typed

theorem LocalTypes.head {n : Nat} {Γ : Ctx Head n} {locals : List (Tm Head n)} (types : LocalTypes Γ locals)
    {h : Fin n} {T : Tm Head n} (looked : locals[h.val]? = some T) : Ctx.lookup Γ h = T := by
  obtain ⟨_, same⟩ := types h.val T looked
  simpa using same

include facts in
theorem spineBase_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : spineBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) : ∀ piece ∈ pieces, piece.Typed S.R Γ := by
  obtain ⟨h, as, bs, ds, E, _, rfl, rfl, _, la, lb, _, looked, rfl⟩ := spineBase_spec found
  obtain ⟨principal, th⟩ := head_principal (S := S) (types.head looked)
  exact spinePieces_typed (spine_typed facts formed ds as E la principal th tl).1
    (spine_typed facts formed ds bs E lb principal th tr).1

include facts roots heads algebra complete in
theorem spineBase_exact {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : spineBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C) :
    Equal S.R Γ left right C ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ := by
  obtain ⟨h, as, bs, ds, E, base, rfl, rfl, _, la, lb, nonempty, looked, rfl⟩ := spineBase_spec found
  exact spine_exact facts roots heads algebra complete formed h (types.head looked) la lb nonempty
    (rigidBase_spec base) tl

include facts roots heads algebra rigid complete in
theorem spineBase_weight {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {locals : List (Tm Head n)}
    (types : LocalTypes Γ locals) {C left right : Tm Head n} {pieces : List (Piece Head n)}
    (found : spineBase locals C left right = some pieces) (tl : TypedEquality.Typed S.R Γ left C)
    (tr : TypedEquality.Typed S.R Γ right C) :
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left C wl ∧ HasWeight S Γ right C wr ∧ w + 2 ≤ wl + wr := by
  obtain ⟨h, as, bs, ds, E, base, rfl, rfl, _, la, lb, _, looked, rfl⟩ := spineBase_spec found
  exact spine_weight facts roots heads algebra rigid complete formed h (types.head looked) la lb
    (rigidBase_spec base) tl tr

include facts in
/-- **The pieces of spines under abstractions are typed.** -/
theorem spineUnder_typed : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    spineUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∀ piece ∈ pieces, piece.Typed S.R Γ
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases spineUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have below := spineUnder_typed _ T l r (formed.snoc ⟨u, hu, tD⟩) (types.under D) computed
          (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        intro piece member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact Piece.typed_under formed ⟨u, hu, tD⟩ (below original inside)
      · exact spineBase_typed facts formed types base tl tr
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
      rcases spineUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact spineBase_typed facts formed types base tl tr

include facts roots heads algebra complete in
/-- **Spines under abstractions decompose exactly** into their pieces, at every formed context. -/
theorem spineUnder_exact : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    spineUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    (Equal S.R Γ left right annotation ↔ ∀ piece ∈ pieces, piece.Holds S.R Γ)
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases spineUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        have below := spineUnder_exact _ T l r formedD (types.under D) computed tl' tr'
        have typed := spineUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
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
      · exact spineBase_exact facts roots heads algebra complete formed types base tl
  | _, locals, .var _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .const _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .head _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .sigma _ _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .id _ _ _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .lam _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .app _ _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .pair _ _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .fst _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .snd _, left, right, Γ, pieces, formed, types, found, tl, _
  | _, locals, .refl _, left, right, Γ, pieces, formed, types, found, tl, _ => by
      rcases spineUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact spineBase_exact facts roots heads algebra complete formed types base tl

include facts roots heads algebra rigid complete in
/-- **Spines under abstractions weigh more than their pieces.** -/
theorem spineUnder_weight : ∀ {n : Nat} (locals : List (Tm Head n)) (annotation left right : Tm Head n)
    {Γ : Ctx Head n} {pieces : List (Piece Head n)}, CtxFormed S.R Γ → LocalTypes Γ locals →
    spineUnder locals annotation left right = some pieces →
    TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
    ∃ w wl wr, PiecesWeigh S Γ pieces w ∧ HasWeight S Γ left annotation wl ∧ HasWeight S Γ right annotation wr ∧
      w + 2 ≤ wl + wr
  | _, locals, .pi D T, left, right, Γ, pieces, formed, types, found, tl, tr => by
      rcases spineUnder_cases found with ⟨D', T', l, r, inner, same, rfl, rfl, computed, rfl⟩ | base
      · injection same with _ sameD sameT
        subst sameD
        subst sameT
        obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
        have isD : IsType S.R Γ D := ⟨u, hu, tD⟩
        have formedD := formed.snoc isD
        have tl' := Typed.lam_inv facts tl formed
        have tr' := Typed.lam_inv facts tr formed
        obtain ⟨w, wl, wr, weighs, left, right, total⟩ :=
          spineUnder_weight _ T l r formedD (types.under D) computed tl' tr'
        have typed := spineUnder_typed facts _ T l r formedD (types.under D) computed tl' tr'
        obtain ⟨v, hv, tPi⟩ := Typed.isType tl formed
        exact ⟨w, wl, wr, PiecesWeigh.under formed isD typed weighs, HasWeight.under (w := v) hv tPi isD left,
          HasWeight.under (w := v) hv tPi isD right, total⟩
      · exact spineBase_weight facts roots heads algebra rigid complete formed types base tl tr
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
      rcases spineUnder_cases found with ⟨_, _, _, _, _, same, _⟩ | base
      · cases same
      · exact spineBase_weight facts roots heads algebra rigid complete formed types base tl tr

end UnderTheory

end ContextualDependentSpinesMany
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
