import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Unfold
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Transitivity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness

/-!
# The executable comparison of a qualified package succeeds eventually on typed equal terms

**The comparison has no cliff where its reducer has none.** For every package with the facts about the
weak-head forms of its types, root and head preservation, the cumulativity algebra and a complete algorithmic
equality (exactly the hypotheses under which the algorithm derives the typed equalities,
`algorithm_iff_equal`; every qualified package has them, and so does the bare tower), and every reducer
that keeps what it returned and that, on every term typed in a formed context, eventually returns a weak-head
normal reduct of it (`WhnfEventually`), the executable comparison accepts every pair of typed terms that are
equal at some budget, and the same certificate at every larger budget (`compare_eventually`); the same holds
for the comparison of types (`types_eventually`).

**How.** The proof follows the derivation of the algorithmic equality of the pair, which completeness
supplies, but asks of the executable's own inputs only that they be equal
to the derivation's: a context of equal types (`CtxEq`), an equal type, and equal terms (`TermsRealized`). The
weak-head forms of equal types have one former with equal components (`FormFacts`), so the executable takes
the branch the derivation takes. Where the executable compares two terms as spines, its terms are the reducer's
weak-head forms, and a second derivation, from completeness for the derivation's spine and the executable's
form, relates them spine by spine (`SpineTo`, `fresh_spine`). The domains of the head's type agree because a
spine's type is principal (`spinesW_pi_domain`). No confluence, joinability, strong normalization or shape of
the reducer's other answers is used.

**Instances.** The tree's full normalizer with a complete root evaluator is such a reducer under strong
normalization of typed terms (`normalize_whnfEventually`), so the comparison over it succeeds eventually on
every such package with that hypothesis (`sn_compare_eventually`, and `normalize_compare_eventually` for a
qualified package).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction ExecutableConversion

/-! ## What the comparison asks of its reducer -/

section Reducers

variable {Head : Type} (R : Rules Head)

/-- **A reducer that keeps what it returned** at every larger budget. -/
def Stable (red : Reducer R) : Prop :=
  ∀ {n : Nat} (fuel : Nat) (t : Tm Head n),
    ContextualDependentConversionBudget.Keeps (red fuel t) (red (fuel + 1) t)

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- **A reducer with no cliff on typed terms**: on every term typed in a formed context it returns, at some
budget and at every larger one, one weak-head normal reduct of the term. -/
def WhnfEventually (S : Setting Head L) (red : Reducer S.R) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n}, CtxFormed S.R Γ → Typed S.R Γ t A →
    ∃ (fuel : Nat) (result : Result S.R t), Whnf S.R S.roles result.val ∧
      ∀ larger, fuel ≤ larger → red larger t = some result

end Reducers

section Mono

variable {Head : Type} {R : Rules Head} [DecidableEq Head] [DecidableRel R.headEq]
  [∀ head, Decidable (R.isUniverse head)] {red : Reducer R} (stable : Stable R red)
variable {n : Nat} {fuel larger : Nat} {Γ : Ctx Head n}
include stable

theorem ok_compare_mono {left right type : Tm Head n} (ok : Ok (compare R red fuel Γ left right type))
    (le : fuel ≤ larger) : Ok (compare R red larger Γ left right type) := by
  obtain ⟨c, h⟩ := ok
  exact ⟨c, ContextualDependentConversionBudget.compare_success_mono R red stable h le⟩

theorem ok_types_mono {left right : Tm Head n} (ok : Ok (types R red fuel Γ left right))
    (le : fuel ≤ larger) : Ok (types R red larger Γ left right) := by
  obtain ⟨c, h⟩ := ok
  exact ⟨c, ContextualDependentConversionBudget.types_success_mono R red stable h le⟩

theorem neutral_mono {left right : Tm Head n} {result : NeutralResult R Γ left right}
    (computed : neutral R red fuel Γ left right = some result) (le : fuel ≤ larger) :
    neutral R red larger Γ left right = some result :=
  ContextualDependentConversionBudget.neutral_success_mono R red stable computed le

end Mono

/-! ## Facts about the algorithmic equality used by the alignment -/

section Facts

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem spineType_typeForm {n : Nat} {A : Tm Head n} (spine : SpineType S.R S.roles A) :
    IsTypeForm S.roles A := by
  rcases spine with ⟨C, a, b, rfl⟩ | neutral | ⟨T, ctors, role, rfl⟩ | ⟨h, rfl, _⟩
  · exact .inr (.inr (.inr (.inl ⟨C, a, b, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl neutral))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))
  · exact .inl ⟨h, rfl⟩

/-- Weak-head form of a type reached by reduction: it is a type form, equal to the type. -/
theorem type_form (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
    {n : Nat} {Γ : Ctx Head n} {A r : Tm Head n}
    (formed : CtxFormed S.R Γ) (isType : IsType S.R Γ A) (path : Reduces S.R A r)
    (normal : Whnf S.R S.roles r) : IsTypeForm S.roles r ∧ TypeEq S.R Γ A r := by
  obtain ⟨u, hu, tA⟩ := isType
  obtain ⟨tr, e⟩ := Reduces.preserve (S := S) facts roots heads formed path tA
  obtain ⟨A', rA', fA'⟩ := facts.typeForm ⟨u, hu, tr⟩ formed
  obtain rfl := whRed_of_whnf S.R normal rA'.red
  exact ⟨fA', u, hu, e⟩

/-- **The reducer's form of a type equal to a type form matches it.** -/
theorem eventually_type (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) {red : Reducer S.R} (eventually : WhnfEventually S red)
    {n : Nat} {Γ : Ctx Head n} {X A₁ : Tm Head n} (formed : CtxFormed S.R Γ)
    (fX : IsTypeForm S.roles X) (eX : TypeEq S.R Γ X A₁) :
    ∃ (fuel : Nat) (v : Tm Head n) (path : Reduces S.R A₁ v),
      (∀ larger, fuel ≤ larger → red larger A₁ = some ⟨v, path⟩) ∧ IsTypeForm S.roles v ∧
        TypeEq S.R Γ A₁ v ∧ FormsMatch S.R S.roles Γ X v := by
  obtain ⟨u, hu, tA₁⟩ := (TypeEq.isType eX formed).2
  obtain ⟨fuel, ⟨v, path⟩, normal, stable⟩ := eventually formed tA₁
  obtain ⟨fv, eAv⟩ := type_form facts roots heads formed ⟨u, hu, tA₁⟩ path normal
  exact ⟨fuel, v, path, stable, fv, eAv, facts.forms (TypeEq.trans S.levels eX eAv) formed fX fv⟩

/-- **The reducer's form of a typed term** is a weak-head form equal to it. -/
theorem eventually_term (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) {red : Reducer S.R} (eventually : WhnfEventually S red)
    {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (formed : CtxFormed S.R Γ) (typed : Typed S.R Γ t A) :
    ∃ (fuel : Nat) (v : Tm Head n) (path : Reduces S.R t v),
      (∀ larger, fuel ≤ larger → red larger t = some ⟨v, path⟩) ∧ Whnf S.R S.roles v ∧
        Equal S.R Γ t v A := by
  obtain ⟨fuel, ⟨v, path⟩, normal, stable⟩ := eventually formed typed
  exact ⟨fuel, v, path, stable, normal, (Reduces.preserve (S := S) facts roots heads formed path typed).2⟩

/-- Applying both sides of an equality of functions to a fresh variable. -/
theorem equal_app_var {n : Nat} {Γ : Ctx Head n} {f g D : Tm Head n} {E : Tm Head (n + 1)}
    (e : Equal S.R Γ f g (.pi D E)) :
    Equal S.R (.snoc Γ D) (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk g) (.var 0)) E := by
  have weakened : Equal S.R (.snoc Γ D) (Presentation.rename wk f) (Presentation.rename wk g)
      (.pi (Presentation.rename wk D) (Presentation.rename (liftRen wk) E)) := Equal.weaken e
  have applied := Derivable.appCong weakened
    (Derivable.refl (Derivable.var 0 : Typed S.R (.snoc Γ D) (.var 0) _))
  rwa [inst0_var_rename_liftRen_wk] at applied

/-! ### Inversions of spine comparisons -/

theorem spines_var_inv {n : Nat} {Γ : Ctx Head n} {i : Fin n} {t₁ V : Tm Head n}
    (e : Algorithmic S.R S.roles (.spines Γ (.var i) t₁ V)) : t₁ = .var i := by
  cases e
  rfl

theorem spines_const_inv {n : Nat} {Γ : Ctx Head n} {name : DeclName} {t₁ V : Tm Head n}
    (e : Algorithmic S.R S.roles (.spines Γ (.const name) t₁ V)) : t₁ = .const name := by
  cases e
  rfl

theorem spines_app_inv {n : Nat} {Γ : Ctx Head n} {f a t₁ V : Tm Head n}
    (e : Algorithmic S.R S.roles (.spines Γ (.app f a) t₁ V)) :
    ∃ f₁ a₁ A' B', t₁ = .app f₁ a₁ ∧ Algorithmic S.R S.roles (.spinesW Γ f f₁ (.pi A' B')) ∧
      Algorithmic S.R S.roles (.terms Γ a a₁ A') := by
  cases e with
  | app e₁ e₂ => exact ⟨_, _, _, _, rfl, e₁, e₂⟩

theorem spines_fst_inv {n : Nat} {Γ : Ctx Head n} {p t₁ V : Tm Head n}
    (e : Algorithmic S.R S.roles (.spines Γ (.fst p) t₁ V)) :
    ∃ p₁ A' B', t₁ = .fst p₁ ∧ Algorithmic S.R S.roles (.spinesW Γ p p₁ (.sigma A' B')) := by
  cases e with
  | fst e₁ => exact ⟨_, _, _, rfl, e₁⟩

theorem spines_snd_inv {n : Nat} {Γ : Ctx Head n} {p t₁ V : Tm Head n}
    (e : Algorithmic S.R S.roles (.spines Γ (.snd p) t₁ V)) :
    ∃ p₁ A' B', t₁ = .snd p₁ ∧ Algorithmic S.R S.roles (.spinesW Γ p p₁ (.sigma A' B')) := by
  cases e with
  | snd e₁ => exact ⟨_, _, _, rfl, e₁⟩

theorem spinesW_inv {n : Nat} {Γ : Ctx Head n} {t u U : Tm Head n}
    (e : Algorithmic S.R S.roles (.spinesW Γ t u U)) :
    ∃ U₀, Algorithmic S.R S.roles (.spines Γ t u U₀) := by
  cases e with
  | spinesW d _ _ => exact ⟨_, d⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra in
/-- **Spine-related terms are equal at every type of the left one**, because the type of a spine is
principal. -/
theorem spines_equal_at {n : Nat} {Γ : Ctx Head n} {t t₁ V X : Tm Head n} (formed : CtxFormed S.R Γ)
    (e : Algorithmic S.R S.roles (.spines Γ t t₁ V)) (typed : Typed S.R Γ t X) :
    Equal S.R Γ t t₁ X ∧ TypeLe S.R Γ V X := by
  obtain ⟨tt, tt₁, _⟩ := Algorithmic.sound facts roots heads algebra e formed
  obtain ⟨_, _, eq, principal, _⟩ :=
    Algorithm.sound facts roots heads algebra e.refines formed tt tt₁
  have le := principal typed
  exact ⟨.subEq eq (TypeLe.toBelow le (Typed.isType typed formed)), le⟩

include facts roots heads algebra in
/-- **The domain a spine comparison gives the head's type is the domain of every function type of the
head.** -/
theorem spinesW_pi_domain {n : Nat} {Γ : Ctx Head n} {f f₁ A' A : Tm Head n} {B' B : Tm Head (n + 1)}
    (formed : CtxFormed S.R Γ) (e : Algorithmic S.R S.roles (.spinesW Γ f f₁ (.pi A' B')))
    (typed : Typed S.R Γ f (.pi A B)) : TypeEq S.R Γ A' A := by
  cases e with
  | spinesW d r _ =>
      obtain ⟨_, le⟩ := spines_equal_at facts roots heads algebra formed d typed
      obtain ⟨A'', B'', eT, eA', _⟩ :=
        Below.pi_source facts (TypeLe.toBelow le (Typed.isType typed formed)) formed r.typeEq
      exact TypeEq.trans S.levels eA' (TypeEq.pi_injective facts eT formed).1.symm

include complete in
/-- **A second derivation at a spine.** A spine of the derivation and a weak-head form equal to it at a
type at which values are compared as spines are related spine by spine, and the form is a spine too. -/
theorem fresh_spine {n : Nat} {Γ : Ctx Head n} {t r A : Tm Head n} (formed : CtxFormed S.R Γ)
    (form : SpineForm S.roles t) (spineType : SpineType S.R S.roles A) (fA : IsTypeForm S.roles A)
    (normal : Whnf S.R S.roles r) (equal : Equal S.R Γ t r A) :
    SpineForm S.roles r ∧ ∃ V, Algorithmic S.R S.roles (.spines Γ t r V) := by
  have d := complete formed equal
  cases d with
  | terms rA _ rt rr d' =>
      obtain rfl := whRed_of_whnf S.R fA.whnf rA.red
      obtain rfl := whRed_of_whnf S.R form.whnf rt.red
      obtain rfl := whRed_of_whnf S.R normal rr.red
      cases d' with
      | univ hu _ _ _ => exact absurd hu spineType.not_universe
      | eta => exact absurd spineType SpineType.not_pi
      | sigmaEta => exact absurd spineType SpineType.not_sigma
      | refl => exact absurd form SpineForm.not_refl
      | spine _ _ fR _ _ dS =>
          obtain ⟨U₀, d₀⟩ := spinesW_inv dS
          exact ⟨fR, U₀, d₀⟩

include facts roots heads algebra complete in
/-- **A second derivation at an identity type**: a weak-head form equal to a reflexivity proof is a
reflexivity proof of an equal subject. -/
theorem fresh_refl {n : Nat} {Γ : Ctx Head n} {x r C a b : Tm Head n} (formed : CtxFormed S.R Γ)
    (normal : Whnf S.R S.roles r) (equal : Equal S.R Γ (.refl x) r (.id C a b)) :
    ∃ x₁, r = .refl x₁ ∧ Equal S.R Γ x x₁ C := by
  have d := complete formed equal
  cases d with
  | terms rA _ rt rr d' =>
      obtain rfl := whRed_of_whnf S.R (id_whnf S.shape C a b) rA.red
      obtain rfl := whRed_of_whnf S.R (refl_whnf S.shape x) rt.red
      obtain rfl := whRed_of_whnf S.R normal rr.red
      cases d' with
      | refl _ _ dx => exact ⟨_, rfl, Algorithmic.sound_terms facts roots heads algebra formed dx⟩
      | spine _ fT _ _ _ _ => exact absurd fT SpineForm.not_refl

include complete in
/-- **A second derivation at neutral types**: a weak-head form equal to a neutral type is related to it
spine by spine. -/
theorem fresh_neutralTypes {n : Nat} {Γ : Ctx Head n} {A r : Tm Head n} (formed : CtxFormed S.R Γ)
    (neutralA : Neutral S.roles A) (normal : Whnf S.R S.roles r) (equal : TypeEq S.R Γ A r) :
    ∃ V, Algorithmic S.R S.roles (.spines Γ A r V) := by
  have d := AlgorithmicComplete.types complete equal formed
  cases d with
  | types rA rB _ _ d' =>
      obtain rfl := whRed_of_whnf S.R (neutralA.whnf S.shape) rA.red
      obtain rfl := whRed_of_whnf S.R normal rB.red
      cases d' with
      | heads => exact absurd rfl (neutralA.not_former.1 _)
      | pi => exact absurd rfl (neutralA.not_former.2.1 _ _)
      | sigma => exact absurd rfl (neutralA.not_former.2.2.1 _ _)
      | id => exact absurd rfl (neutralA.not_former.2.2.2 _ _ _)
      | inductiveType role _ => exact absurd rfl (neutralA.ne_inductive role)
      | neutralTypes _ _ _ dS => exact spinesW_inv dS

end Facts

/-! ## The alignment -/

section Realization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]

variable (S) in
/-- The executable's inputs at a spine: spines the algorithmic equality relates to the derivation's. -/
def SpineTo {n : Nat} (Γ : Ctx Head n) (t t₁ : Tm Head n) : Prop :=
  ∃ V, Algorithmic S.R S.roles (.spines Γ t t₁ V)

variable (red : Reducer S.R)

/-- Type comparison succeeds on all inputs equal to the given ones, in a context of equal types. -/
def TypesRealized {n : Nat} (Γ : Ctx Head n) (A B : Tm Head n) : Prop :=
  ∀ {Γ₁ : Ctx Head n} {A₁ B₁ : Tm Head n}, CtxEq S.R Γ Γ₁ → CtxFormed S.R Γ₁ →
    TypeEq S.R Γ₁ A A₁ → TypeEq S.R Γ₁ B B₁ → ∃ fuel, Ok (types S.R red fuel Γ₁ A₁ B₁)

/-- Term comparison succeeds on all inputs equal to the given ones, at an equal type, in a context of
equal types. -/
def TermsRealized {n : Nat} (Γ : Ctx Head n) (t u A : Tm Head n) : Prop :=
  ∀ {Γ₁ : Ctx Head n} {t₁ u₁ A₁ : Tm Head n}, CtxEq S.R Γ Γ₁ → CtxFormed S.R Γ₁ →
    TypeEq S.R Γ₁ A A₁ → Equal S.R Γ₁ t t₁ A₁ → Equal S.R Γ₁ u u₁ A₁ →
    ∃ fuel, Ok (compare S.R red fuel Γ₁ t₁ u₁ A₁)

/-- Spine comparison succeeds on all spines related to the given ones and returns a type equal to the
derivation's. -/
def SpinesRealized {n : Nat} (Γ : Ctx Head n) (t u U : Tm Head n) : Prop :=
  ∀ {Γ₁ : Ctx Head n} {t₁ u₁ : Tm Head n}, CtxEq S.R Γ Γ₁ → CtxFormed S.R Γ₁ →
    SpineTo S Γ₁ t t₁ → SpineTo S Γ₁ u u₁ →
    ∃ fuel T certificate, neutral S.R red fuel Γ₁ t₁ u₁ = some ⟨T, certificate⟩ ∧ TypeEq S.R Γ₁ U T

/-- What each judgment of the algorithmic equality guarantees about the executable. -/
def Realized : AlgorithmicStatement Head → Prop
  | .types Γ A B => TypesRealized red Γ A B
  | .typesW Γ A B => TypesRealized red Γ A B
  | .terms Γ t u A => TermsRealized red Γ t u A
  | .termsW Γ t u A => TermsRealized red Γ t u A
  | .spines Γ t u U => SpinesRealized red Γ t u U
  | .spinesW Γ t u U => SpinesRealized red Γ t u U

variable {red}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (stable : Stable S.R red) (eventually : WhnfEventually S red)
include facts roots heads algebra complete stable eventually

/-- **Every derivation of the algorithmic equality is realized by the executable comparison**, on all
inputs equal to its own. -/
theorem realized {st : AlgorithmicStatement Head} (derivation : Algorithmic S.R S.roles st) :
    Realized red st := by
  have conv := fun {st : AlgorithmicStatement Head} (d : Algorithmic S.R S.roles st) =>
    Algorithmic.converts facts roots heads algebra d
  induction derivation with
  | types rA rB _ _ _ ih =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      exact (ih : TypesRealized red _ _ _) equal formed
        (TypeEq.trans S.levels (rA.stable equal).typeEq.symm eA)
        (TypeEq.trans S.levels (rB.stable equal).typeEq.symm eB)
  | @heads n Γ h h' u same _ _ _ =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ := eventually_type facts roots heads eventually formed (.inl ⟨h, rfl⟩) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, _, m₂⟩ := eventually_type facts roots heads eventually formed (.inl ⟨h', rfl⟩) eB
      obtain ⟨h₁, rfl, s₁⟩ := m₁.head_left
      obtain ⟨h₂, rfl, s₂⟩ := m₂.head_left
      have same' : HeadSame S.R h₁ h₂ :=
        HeadSame.trans S.levels (HeadSame.symm S.levels s₁) (HeadSame.trans S.levels same s₂)
      exact ⟨f₁ + f₂ + 1, types_heads S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega)) same'⟩
  | @pi n Γ A A' B B' _ dA _ ihA ihB =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inl ⟨A, B, rfl⟩)) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, _, m₂⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inl ⟨A', B', rfl⟩)) eB
      obtain ⟨D, E, rfl, eAD, eBE⟩ := m₁.pi_left
      obtain ⟨D', E', rfl, eAD', eBE'⟩ := m₂.pi_left
      have eAA' : TypeEq S.R Γ₁ A A' :=
        Algorithmic.sound_types facts roots heads algebra formed (conv dA equal formed)
      have isD := (TypeEq.isType eAD formed).2
      obtain ⟨g₁, hg₁⟩ := (ihA : TypesRealized red _ _ _) equal formed eAD eAD'
      have eB₁ : TypeEq S.R (.snoc Γ₁ D) B E := eBE.stable (.snoc (CtxEq.refl Γ₁ formed) eAD.symm)
      have eB₂ : TypeEq S.R (.snoc Γ₁ D) B' E' :=
        eBE'.stable (.snoc (CtxEq.refl Γ₁ formed) (TypeEq.trans S.levels eAD.symm eAA'))
      obtain ⟨g₂, hg₂⟩ := (ihB : TypesRealized red _ _ _) (.snoc equal eAD.symm) (.snoc formed isD) eB₁ eB₂
      exact ⟨f₁ + f₂ + g₁ + g₂ + 1, types_pi S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (ok_types_mono stable hg₁ (by omega)) (ok_types_mono stable hg₂ (by omega))⟩
  | @sigma n Γ A A' B B' _ dA _ ihA ihB =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inl ⟨A, B, rfl⟩))) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, _, m₂⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inl ⟨A', B', rfl⟩))) eB
      obtain ⟨D, E, rfl, eAD, eBE⟩ := m₁.sigma_left
      obtain ⟨D', E', rfl, eAD', eBE'⟩ := m₂.sigma_left
      have eAA' : TypeEq S.R Γ₁ A A' :=
        Algorithmic.sound_types facts roots heads algebra formed (conv dA equal formed)
      have isD := (TypeEq.isType eAD formed).2
      obtain ⟨g₁, hg₁⟩ := (ihA : TypesRealized red _ _ _) equal formed eAD eAD'
      have eB₁ : TypeEq S.R (.snoc Γ₁ D) B E := eBE.stable (.snoc (CtxEq.refl Γ₁ formed) eAD.symm)
      have eB₂ : TypeEq S.R (.snoc Γ₁ D) B' E' :=
        eBE'.stable (.snoc (CtxEq.refl Γ₁ formed) (TypeEq.trans S.levels eAD.symm eAA'))
      obtain ⟨g₂, hg₂⟩ := (ihB : TypesRealized red _ _ _) (.snoc equal eAD.symm) (.snoc formed isD) eB₁ eB₂
      exact ⟨f₁ + f₂ + g₁ + g₂ + 1, types_sigma S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (ok_types_mono stable hg₁ (by omega)) (ok_types_mono stable hg₂ (by omega))⟩
  | @id n Γ A A' x x' y y' dA _ _ ihA ihx ihy =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inl ⟨A, x, y, rfl⟩)))) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, _, m₂⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inl ⟨A', x', y', rfl⟩)))) eB
      obtain ⟨C, a, b, rfl, eAC, exa, eyb⟩ := m₁.id_left
      obtain ⟨C', a', b', rfl, eAC', exa', eyb'⟩ := m₂.id_left
      have eAA' : TypeEq S.R Γ₁ A A' :=
        Algorithmic.sound_types facts roots heads algebra formed (conv dA equal formed)
      have eA'C : TypeEq S.R Γ₁ A' C := TypeEq.trans S.levels eAA'.symm eAC
      obtain ⟨g₁, hg₁⟩ := (ihA : TypesRealized red _ _ _) equal formed eAC eAC'
      obtain ⟨g₂, hg₂⟩ := (ihx : TermsRealized red _ _ _ _) equal formed eAC (Equal.convType exa eAC)
        (Equal.convType exa' eA'C)
      obtain ⟨g₃, hg₃⟩ := (ihy : TermsRealized red _ _ _ _) equal formed eAC (Equal.convType eyb eAC)
        (Equal.convType eyb' eA'C)
      exact ⟨f₁ + f₂ + g₁ + g₂ + g₃ + 1, types_id S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (ok_types_mono stable hg₁ (by omega)) (ok_compare_mono stable hg₂ (by omega))
        (ok_compare_mono stable hg₃ (by omega))⟩
  | @inductiveType n Γ T ctors role isT =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, _, m₂⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inr (.inr ⟨T, ctors, role, rfl⟩))))) eB
      obtain rfl := m₁.inductive_left role
      obtain rfl := m₂.inductive_left role
      obtain ⟨_, _, typed⟩ := isT
      obtain ⟨_, _, declared, _⟩ := Typed.generation typed
      obtain ⟨certificate, computed⟩ := neutral_const S.R red (fuel := 0) (Γ := Γ₁) declared
      exact ⟨f₁ + f₂ + 2, types_other S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (NotFormer.const T) ⟨_, neutral_mono stable computed (by omega)⟩⟩
  | @neutralTypes n Γ A B u nA nB _ _ ih =>
      intro Γ₁ A₁ B₁ equal formed eA eB
      obtain ⟨f₁, c₁, p₁, stable₁, _, eA₁, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inr (.inl nA))))) eA
      obtain ⟨f₂, c₂, p₂, stable₂, _, eB₁, m₂⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inr (.inl nB))))) eB
      have n₁ : Neutral S.roles c₁ := m₁.neutral_left nA
      have n₂ : Neutral S.roles c₂ := m₂.neutral_left nB
      have to₁ := fresh_neutralTypes complete formed nA (n₁.whnf S.shape) (TypeEq.trans S.levels eA eA₁)
      have to₂ := fresh_neutralTypes complete formed nB (n₂.whnf S.shape) (TypeEq.trans S.levels eB eB₁)
      obtain ⟨g, T, certificate, computed, _⟩ := (ih : SpinesRealized red _ _ _ _) equal formed to₁ to₂
      exact ⟨f₁ + f₂ + g + 1, types_other S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (NotFormer.of_neutral n₁) ⟨_, neutral_mono stable computed (by omega)⟩⟩
  | terms rA _ rt ru _ ih =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      have eA' := TypeEq.trans S.levels (rA.stable equal).typeEq.symm eA
      exact (ih : TermsRealized red _ _ _ _) equal formed eA'
        (.trans (Equal.convType (.symm (rt.stable equal).equal) eA') et)
        (.trans (Equal.convType (.symm (ru.stable equal).equal) eA') eu)
  | @univ n Γ t u h hu _ _ _ ih =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      obtain ⟨f₁, c₁, p₁, stable₁, _, _, m₁⟩ := eventually_type facts roots heads eventually formed (.inl ⟨h, rfl⟩) eA
      obtain ⟨h₁, rfl, same⟩ := m₁.head_left
      have hu₁ : S.R.isUniverse h₁ := (HeadSame.level S.levels same).1.mp hu
      obtain ⟨g, hg⟩ := (ih : TypesRealized red _ _ _) equal formed ⟨h, hu, Equal.convType et eA.symm⟩
        ⟨h, hu, Equal.convType eu eA.symm⟩
      exact ⟨f₁ + g + 1, compare_universe S.R red hu₁ (stable₁ _ (by omega))
        (ok_types_mono stable hg (by omega))⟩
  | @eta n Γ f g A B _ _ _ _ _ _ ih =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      obtain ⟨f₁, c₁, p₁, stable₁, _, eA₁, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inl ⟨A, B, rfl⟩)) eA
      obtain ⟨D, E, rfl, eAD, eBE⟩ := m₁.pi_left
      have isD := (TypeEq.isType eAD formed).2
      have eB₁ : TypeEq S.R (.snoc Γ₁ D) B E := eBE.stable (.snoc (CtxEq.refl Γ₁ formed) eAD.symm)
      obtain ⟨g', hg⟩ := (ih : TermsRealized red _ _ _ _) (.snoc equal eAD.symm) (.snoc formed isD) eB₁
        (equal_app_var (Equal.convType et eA₁)) (equal_app_var (Equal.convType eu eA₁))
      exact ⟨f₁ + g' + 1, compare_pi S.R red (stable₁ _ (by omega)) (ok_compare_mono stable hg (by omega))⟩
  | @sigmaEta n Γ p q' A B tp _ _ _ d₁ _ ih₁ ih₂ =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      obtain ⟨f₁, c₁, p₁, stable₁, _, eA₁, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inl ⟨A, B, rfl⟩))) eA
      obtain ⟨D, E, rfl, eAD, eBE⟩ := m₁.sigma_left
      have et' := Equal.convType et eA₁
      have eu' := Equal.convType eu eA₁
      obtain ⟨g₁, hg₁⟩ := (ih₁ : TermsRealized red _ _ _ _) equal formed eAD (.fstCong et') (.fstCong eu')
      have isA := (TypeEq.isType eAD formed).1
      have tfst : Typed S.R Γ₁ (.fst p) A := .fstElim (Typed.stable tp equal)
      have efst : Equal S.R Γ₁ (.fst p) (.fst t₁) A := Equal.convType (.fstCong et') eAD.symm
      have eFst : Equal S.R Γ₁ (.fst p) (.fst q') A :=
        Algorithmic.sound_terms facts roots heads algebra formed (conv d₁ equal formed isA.refl)
      have efstu : Equal S.R Γ₁ (.fst q') (.fst t₁) A := .trans (.symm eFst) efst
      have tfstq : Typed S.R Γ₁ (.fst q') A := (Equal.typed eFst formed).2
      obtain ⟨_, v, hv, tE⟩ := IsType.sigma_parts (TypeEq.isType eA₁ formed).2
      have tE' : Typed S.R (.snoc Γ₁ A) E (.head v) := Typed.stable tE (.snoc (CtxEq.refl Γ₁ formed) eAD)
      have eSnd : TypeEq S.R Γ₁ (inst0 (.fst p) B) (inst0 (.fst t₁) E) :=
        TypeEq.trans S.levels (TypeEq.instantiate eBE tfst) (TypeEq.of_instantiateEq tE' hv tfst efst)
      obtain ⟨g₂, hg₂⟩ := (ih₂ : TermsRealized red _ _ _ _) equal formed eSnd
        (Equal.convType (.sndCong et') (TypeEq.of_instantiateEq tE' hv tfst efst))
        (Equal.convType (.sndCong eu') (TypeEq.of_instantiateEq tE' hv tfstq efstu))
      exact ⟨f₁ + g₁ + g₂ + 1, compare_sigma S.R red (stable₁ _ (by omega))
        (ok_compare_mono stable hg₁ (by omega)) (ok_compare_mono stable hg₂ (by omega))⟩
  | @refl n Γ x x' A a b _ _ _ ih =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      obtain ⟨f₁, c₁, p₁, stable₁, _, eA₁, m₁⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inr (.inl ⟨A, a, b, rfl⟩)))) eA
      obtain ⟨C, a₂, b₂, rfl, eAC, _, _⟩ := m₁.id_left
      obtain ⟨f₂, r₂, p₂, stable₂, w₂, e₂⟩ := eventually_term facts roots heads eventually formed (Equal.typed et formed).2
      obtain ⟨f₃, r₃, p₃, stable₃, w₃, e₃⟩ := eventually_term facts roots heads eventually formed (Equal.typed eu formed).2
      obtain ⟨x₁, rfl, ex⟩ := fresh_refl facts roots heads algebra complete formed w₂ (Equal.convType (.trans et e₂) eA₁)
      obtain ⟨x₂, rfl, ex'⟩ := fresh_refl facts roots heads algebra complete formed w₃ (Equal.convType (.trans eu e₃) eA₁)
      obtain ⟨g, hg⟩ := (ih : TermsRealized red _ _ _ _) equal formed eAC ex ex'
      exact ⟨f₁ + f₂ + f₃ + g + 1, compare_refl S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
        (stable₃ _ (by omega)) (ok_compare_mono stable hg (by omega))⟩
  | @spine n Γ t u A U sA fT fU _ _ _ ih =>
      intro Γ₁ t₁ u₁ A₁ equal formed eA et eu
      obtain ⟨f₁, c₁, p₁, stable₁, fc, eA₁, m₁⟩ :=
        eventually_type facts roots heads eventually formed (spineType_typeForm sA) eA
      have sc : SpineType S.R S.roles c₁ :=
        sA.of_typeEq facts (TypeEq.trans S.levels eA eA₁) formed fc
      obtain ⟨f₂, r₂, p₂, stable₂, w₂, e₂⟩ := eventually_term facts roots heads eventually formed (Equal.typed et formed).2
      obtain ⟨f₃, r₃, p₃, stable₃, w₃, e₃⟩ := eventually_term facts roots heads eventually formed (Equal.typed eu formed).2
      obtain ⟨fR₂, to₂⟩ :=
        fresh_spine complete formed fT sc fc w₂ (Equal.convType (.trans et e₂) eA₁)
      obtain ⟨fR₃, to₃⟩ :=
        fresh_spine complete formed fU sc fc w₃ (Equal.convType (.trans eu e₃) eA₁)
      obtain ⟨g, T, certificate, computed, _⟩ := (ih : SpinesRealized red _ _ _ _) equal formed to₂ to₃
      have neutralOk : Ok (compareNeutral S.R red (f₁ + f₂ + f₃ + g + 1) Γ₁ t₁ u₁ A₁) :=
        compareNeutral_of S.R red (stable₂ _ (by omega)) (stable₃ _ (by omega))
          ⟨_, neutral_mono stable computed (by omega)⟩
      refine ⟨f₁ + f₂ + f₃ + g + 2, ?_⟩
      rcases sc with ⟨C, a, b, rfl⟩ | nc | ⟨T', ctors, role, rfl⟩ | ⟨h, rfl, notUniverse⟩
      · have notRefl : ∀ x, r₂ ≠ .refl x := fun x same => SpineForm.not_refl (same ▸ fR₂)
        exact compare_id_spine S.R red (stable₁ _ (by omega)) (stable₂ _ (by omega))
          (stable₃ _ (by omega)) notRefl neutralOk
      · exact compare_other S.R red (NotFormer.of_neutral nc) (stable₁ _ (by omega)) neutralOk
      · exact compare_other S.R red (NotFormer.const T') (stable₁ _ (by omega)) neutralOk
      · exact compare_ground S.R red notUniverse (stable₁ _ (by omega)) neutralOk
  | @var n Γ i =>
      intro Γ₁ t₁ u₁ equal _ ⟨V, e⟩ ⟨V', e'⟩
      obtain rfl := spines_var_inv e
      obtain rfl := spines_var_inv e'
      obtain ⟨certificate, computed⟩ := neutral_var S.R red (fuel := 0) (Γ := Γ₁) i
      exact ⟨1, _, certificate, computed, (equal.lookup i).symm⟩
  | @const n Γ name type declared typed =>
      intro Γ₁ t₁ u₁ equal formed ⟨V, e⟩ ⟨V', e'⟩
      obtain rfl := spines_const_inv e
      obtain rfl := spines_const_inv e'
      obtain ⟨certificate, computed⟩ := neutral_const S.R red (fuel := 0) (Γ := Γ₁) declared
      exact ⟨1, _, certificate, computed, IsType.refl (Typed.isType (Typed.stable typed equal) formed)⟩
  | @app n Γ f g a b A B d₁ _ ih₁ ih₂ =>
      intro Γ₁ t₁ u₁ equal formed ⟨V, e⟩ ⟨V', e'⟩
      obtain ⟨f₁, a₁, A', B', rfl, e₁, e₂⟩ := spines_app_inv e
      obtain ⟨g₁, b₁, A'', B'', rfl, e₁', e₂'⟩ := spines_app_inv e'
      obtain ⟨gf, T, certificate, computed, eT⟩ :=
        (ih₁ : SpinesRealized red _ _ _ _) equal formed (spinesW_inv e₁) (spinesW_inv e₁')
      obtain ⟨fT, c, pc, stableT, _, eTc, mT⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inl ⟨A, B, rfl⟩)) eT
      obtain ⟨D, E, rfl, eAD, eBE⟩ := mT.pi_left
      obtain ⟨U', d₁', eU'⟩ := conv d₁ equal formed
      obtain ⟨tf, tg, _⟩ := Algorithmic.sound facts roots heads algebra d₁' formed
      have eA'A := spinesW_pi_domain facts roots heads algebra formed e₁ (Typed.convType tf eU'.symm)
      have eA''A := spinesW_pi_domain facts roots heads algebra formed e₁' (Typed.convType tg eU'.symm)
      have ea : Equal S.R Γ₁ a a₁ A :=
        Equal.convType (Algorithmic.sound_terms facts roots heads algebra formed e₂) eA'A
      have eb : Equal S.R Γ₁ b b₁ A :=
        Equal.convType (Algorithmic.sound_terms facts roots heads algebra formed e₂') eA''A
      obtain ⟨gArg, hArg⟩ := (ih₂ : TermsRealized red _ _ _ _) equal formed eAD (Equal.convType ea eAD)
        (Equal.convType eb eAD)
      obtain ⟨certificate', result⟩ := neutral_app S.R red (fuel := gf + fT + gArg)
        (neutral_mono stable computed (by omega)) (stableT _ (by omega)) (ok_compare_mono stable hArg (by omega))
      have ta : Typed S.R Γ₁ a A := (Equal.typed ea formed).1
      obtain ⟨_, v, hv, tE⟩ := IsType.pi_parts (TypeEq.isType eTc formed).2
      have tE' : Typed S.R (.snoc Γ₁ A) E (.head v) := Typed.stable tE (.snoc (CtxEq.refl Γ₁ formed) eAD)
      exact ⟨_, _, certificate', result,
        TypeEq.trans S.levels (TypeEq.instantiate eBE ta) (TypeEq.of_instantiateEq tE' hv ta ea)⟩
  | @fst n Γ p q' A B _ ih =>
      intro Γ₁ t₁ u₁ equal formed ⟨V, e⟩ ⟨V', e'⟩
      obtain ⟨p₁, A', B', rfl, e₁⟩ := spines_fst_inv e
      obtain ⟨q₁, A'', B'', rfl, e₁'⟩ := spines_fst_inv e'
      obtain ⟨gp, T, certificate, computed, eT⟩ :=
        (ih : SpinesRealized red _ _ _ _) equal formed (spinesW_inv e₁) (spinesW_inv e₁')
      obtain ⟨fT, c, pc, stableT, _, _, mT⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inl ⟨A, B, rfl⟩))) eT
      obtain ⟨D, E, rfl, eAD, _⟩ := mT.sigma_left
      obtain ⟨certificate', result⟩ := neutral_fst S.R red (fuel := gp + fT)
        (neutral_mono stable computed (by omega)) (stableT _ (by omega))
      exact ⟨_, _, certificate', result, eAD⟩
  | @snd n Γ p q' A B d ih =>
      intro Γ₁ t₁ u₁ equal formed ⟨V, e⟩ ⟨V', e'⟩
      obtain ⟨p₁, A', B', rfl, e₁⟩ := spines_snd_inv e
      obtain ⟨q₁, A'', B'', rfl, e₁'⟩ := spines_snd_inv e'
      obtain ⟨gp, T, certificate, computed, eT⟩ :=
        (ih : SpinesRealized red _ _ _ _) equal formed (spinesW_inv e₁) (spinesW_inv e₁')
      obtain ⟨fT, c, pc, stableT, _, eTc, mT⟩ :=
        eventually_type facts roots heads eventually formed (.inr (.inr (.inl ⟨A, B, rfl⟩))) eT
      obtain ⟨D, E, rfl, eAD, eBE⟩ := mT.sigma_left
      obtain ⟨certificate', result⟩ := neutral_snd S.R red (fuel := gp + fT)
        (neutral_mono stable computed (by omega)) (stableT _ (by omega))
      obtain ⟨U', d', eU'⟩ := conv d equal formed
      obtain ⟨tp, _, _⟩ := Algorithmic.sound facts roots heads algebra d' formed
      have tpS : Typed S.R Γ₁ p (.sigma A B) := Typed.convType tp eU'.symm
      have tfst : Typed S.R Γ₁ (.fst p) A := .fstElim tpS
      obtain ⟨U₀, e₀⟩ := spinesW_inv e₁
      obtain ⟨epp, _⟩ := spines_equal_at facts roots heads algebra formed e₀ tpS
      obtain ⟨_, v, hv, tE⟩ := IsType.sigma_parts (TypeEq.isType eTc formed).2
      have tE' : Typed S.R (.snoc Γ₁ A) E (.head v) := Typed.stable tE (.snoc (CtxEq.refl Γ₁ formed) eAD)
      exact ⟨_, _, certificate', result, TypeEq.trans S.levels (TypeEq.instantiate eBE tfst)
        (TypeEq.of_instantiateEq tE' hv tfst (.fstCong epp))⟩
  | spinesW _ rU _ ih =>
      intro Γ₁ t₁ u₁ equal formed to₁ to₂
      obtain ⟨g, T, certificate, computed, eT⟩ := (ih : SpinesRealized red _ _ _ _) equal formed to₁ to₂
      exact ⟨g, T, certificate, computed, TypeEq.trans S.levels (rU.stable equal).typeEq.symm eT⟩

/-! ## Eventual success -/

/-- **Items 1 and 4 for comparison**: for every package whose weak-head forms of types have the facts of
the normalization model and whose algorithmic equality is complete (the hypotheses under which the
algorithm derives exactly the typed equalities, `algorithm_iff_equal`), with a reducer that keeps its answers
and eventually returns a weak-head normal reduct of every typed term, the executable comparison accepts
every pair of equal typed terms at some budget and keeps its certificate at every larger budget. -/
theorem compare_eventually {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n} (formed : CtxFormed S.R Γ)
    (equal : Equal S.R Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger → compare S.R red larger Γ t u A = some certificate := by
  obtain ⟨tt, tu⟩ := Equal.typed equal formed
  obtain ⟨fuel, certificate, computed⟩ :=
    (realized facts roots heads algebra complete stable eventually (complete formed equal) : TermsRealized red _ _ _ _)
      (CtxEq.refl Γ formed) formed (Typed.isType tt formed).refl (.refl tt) (.refl tu)
  exact ⟨fuel, certificate, fun _ enough =>
    ContextualDependentConversionBudget.compare_success_mono S.R red stable computed enough⟩

/-- **Type comparison**: every equality of types of a formed context is accepted at some budget, with the
same certificate at every larger budget. -/
theorem types_eventually {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} (formed : CtxFormed S.R Γ)
    (equal : TypeEq S.R Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger → types S.R red larger Γ A B = some certificate := by
  obtain ⟨isA, isB⟩ := TypeEq.isType equal formed
  obtain ⟨fuel, certificate, computed⟩ :=
    (realized facts roots heads algebra complete stable eventually (AlgorithmicComplete.types complete equal formed) :
      TypesRealized red _ _ _) (CtxEq.refl Γ formed) formed isA.refl isB.refl
  exact ⟨fuel, certificate, fun _ enough =>
    ContextualDependentConversionBudget.types_success_mono S.R red stable computed enough⟩

end Realization

/-! ## The full normalizer is such a reducer under strong normalization -/

section FullNormalizer

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] in
/-- The tree's normalizer keeps its answers. -/
theorem normalize_stable (root : RootEvaluator S.R) : Stable S.R (normalize S.R root) :=
  fun fuel t => ContextualDependentConversionBudget.normalizer_stable S.R root fuel t

omit [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)] in
/-- **Under strong normalization of typed terms, the full normalizer with a complete root evaluator has no
cliff on typed terms**: its answer is directed normal, hence weak-head normal. -/
theorem normalize_whnfEventually (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (rootComplete : RootComplete S.R root) : WhnfEventually S (normalize S.R root) := by
  intro n Γ t A formed typed
  obtain ⟨fuel, result, normal, _, stable⟩ :=
    typed_normalize_eventually S.R root sn rootComplete formed typed
  exact ⟨fuel, result, whnf_of_normal S.R normal, stable⟩

/-- **The comparison over the full normalizer**, for every package with the algorithmic equality's facts,
strongly normalizing typed terms and a complete root evaluator: every pair of equal typed terms is accepted
at some budget and at every larger one. -/
theorem sn_compare_eventually (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    (complete : AlgorithmicComplete S.R S.roles) (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (rootComplete : RootComplete S.R root) {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (equal : Equal S.R Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare S.R (normalize S.R root) larger Γ t u A = some certificate :=
  compare_eventually facts roots heads algebra complete (normalize_stable root)
    (normalize_whnfEventually sn root rootComplete) formed equal

/-- **Type comparison over the full normalizer**, under the same hypotheses. -/
theorem sn_types_eventually (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
    (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    (complete : AlgorithmicComplete S.R S.roles) (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (rootComplete : RootComplete S.R root) {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (equal : TypeEq S.R Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types S.R (normalize S.R root) larger Γ A B = some certificate :=
  types_eventually facts roots heads algebra complete (normalize_stable root)
    (normalize_whnfEventually sn root rootComplete) formed equal

/-- **On a qualified package**: the comparison over the full normalizer, under strong normalization of
typed terms and with a complete root evaluator. -/
theorem normalize_compare_eventually (q : Qualified S) (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (rootComplete : RootComplete S.R root) {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (equal : Equal S.R Γ t u A) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      compare S.R (normalize S.R root) larger Γ t u A = some certificate :=
  sn_compare_eventually q.facts q.roots q.heads q.algebra q.complete sn root rootComplete formed equal

/-- **On a qualified package**: type comparison over the full normalizer. -/
theorem normalize_types_eventually (q : Qualified S) (sn : TypedSN S.R) (root : RootEvaluator S.R)
    (rootComplete : RootComplete S.R root) {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (equal : TypeEq S.R Γ A B) :
    ∃ fuel certificate, ∀ larger, fuel ≤ larger →
      types S.R (normalize S.R root) larger Γ A B = some certificate :=
  sn_types_eventually q.facts q.roots q.heads q.algebra q.complete sn root rootComplete formed equal

end FullNormalizer

end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms ok_compare_mono
#print axioms type_form
#print axioms eventually_type
#print axioms eventually_term
#print axioms equal_app_var
#print axioms spines_app_inv
#print axioms spines_equal_at
#print axioms spinesW_pi_domain
#print axioms fresh_spine
#print axioms fresh_refl
#print axioms fresh_neutralTypes
#print axioms realized
#print axioms compare_eventually
#print axioms types_eventually
#print axioms normalize_stable
#print axioms normalize_whnfEventually
#print axioms sn_compare_eventually
#print axioms sn_types_eventually
#print axioms normalize_compare_eventually
#print axioms normalize_types_eventually
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
