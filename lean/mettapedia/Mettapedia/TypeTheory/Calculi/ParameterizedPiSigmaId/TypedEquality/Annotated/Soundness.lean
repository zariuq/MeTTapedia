import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Judgment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchLaws

/-!
# Soundness of the annotated calculus in the domain

Every derivable statement of an annotated rule package holds in the domain, for every
reading of its heads and constants that validates the package (`CDerivable.sound`).
The universes are flattened: every universe denotes the universe `U` (Carneiro,
Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès and Weirich, *Definitional
Inversion, Without Normalisation*, §3), so cumulativity and head equality are
equalities of denotations and subtyping is interpreted by equality.

**What a statement means** (`CStatement.Sound`), in every environment that fits the
context (`Fits`):

* **typing**: the type denotes a type-generated ideal, the term denotes an element of
  it (it is fixed by the projection onto the type), and the term has the spine facts
  of a typing at the type (`SpineFacts`);
* **equality**: the two sides denote alike, at a type-generated type of which they are
  elements;
* **subtyping**: the two types denote alike.

**Spine facts.** A declared constant has its declared type; an application of a
function of a dependent function type, whose argument is an element of the domain,
has the family's value at the argument; a reflexivity has an identity type between
its point and itself. The facts recur through the function, the argument and the
point, which carry their typing. So along a spine of a declared constant the
declared type instantiated at the arguments is the type, each argument is an element
of its parameter type with its own facts there (`SpineFacts.constSpine`), and an
argument that is a reflexivity has as parameter type an identity type between its
point and itself (`SpineFacts.reflArg`): the model's identity types do not supply
this, since the reflexivity at the least element is an element of every identity
type.

**Validity of a reading** (`ReadingValid`): universes denote the universe; a head
typed by a head denotes a type and its type the universe; joins of universes,
cumulativity and head equality are respected; a declared constant denotes an element
of its declared type; and a root step relates two terms that denote alike wherever
both are elements of one type-generated type with their spine facts there. For a rule
package with a level model, the conditions on heads reduce to universes denoting the
universe, heads denoting types, and head equality (`ReadingValid.ofLevels`).

**The soundness facts** of the relation's compatibility lemmas (`SoundnessFacts`)
hold for every valid reading (`ReadingValid.soundnessFacts`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypeGenerated principal univIdeal Cont cpi csigma clam instPi
  SpineTyped)
open Normalization (LevelModel)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Definitions -/

section Definitions

variable (Rd : Reading Head)

/-- An environment fits an annotated context: each value is an element of the
denotation of its type, which is type-generated. -/
def Fits : {n : Nat} → CCtx Head n → Env n → Prop
  | _, .nil, _ => True
  | _, .snoc Γ A, ρ => Fits Γ (fun i => ρ i.succ) ∧
      TypeGenerated (cinterp Rd A (fun i => ρ i.succ)) ∧
      projT (cinterp Rd A (fun i => ρ i.succ)) (ρ 0) = ρ 0

variable (P : ChurchRules R)

/-- **Spine facts** of a term at a type: a declared constant has its declared type; an
application has the value, at its argument, of the family of a dependent function
type of which its function is an element, its argument an element of the domain; a
reflexivity has an identity type between its point and itself, its point an element of
the carrier. Function, argument and point have their own spine facts there. -/
def SpineFacts : {n : Nat} → CTm Head n → Ideal → Env n → Prop
  | _, .const c, τ, _ => ∀ D, P.constantType c = some D → τ = cinterp Rd D Env.nil
  | _, .app f a, τ, ρ => ∃ (T : Ideal) (G : Ideal → Ideal), Cont G ∧ τ = G (cinterp Rd a ρ) ∧
      (projT (cpi T G) (cinterp Rd f ρ) = cinterp Rd f ρ ∧ SpineFacts f (cpi T G) ρ) ∧
      (projT T (cinterp Rd a ρ) = cinterp Rd a ρ ∧ SpineFacts a T ρ)
  | _, .refl a, τ, ρ => ∃ T : Ideal, τ = Ideal.ident T (cinterp Rd a ρ) (cinterp Rd a ρ) ∧
      projT T (cinterp Rd a ρ) = cinterp Rd a ρ ∧ SpineFacts a T ρ
  | _, .var _, _, _ => True
  | _, .head _, _, _ => True
  | _, .pi _ _, _, _ => True
  | _, .sigma _ _, _, _ => True
  | _, .id _ _ _, _, _ => True
  | _, .lam _ _, _, _ => True
  | _, .pair _ _, _, _ => True
  | _, .fst _, _, _ => True
  | _, .snd _, _, _ => True

/-- What a derivable annotated statement means in the domain. -/
def CStatement.Sound : CStatement Head → Prop
  | .typing Γ t A => ∀ ρ, Fits Rd Γ ρ →
      TypeGenerated (cinterp Rd A ρ) ∧ projT (cinterp Rd A ρ) (cinterp Rd t ρ) = cinterp Rd t ρ ∧
        SpineFacts Rd P t (cinterp Rd A ρ) ρ
  | .equality Γ a b A => ∀ ρ, Fits Rd Γ ρ →
      cinterp Rd a ρ = cinterp Rd b ρ ∧ TypeGenerated (cinterp Rd A ρ) ∧
        projT (cinterp Rd A ρ) (cinterp Rd a ρ) = cinterp Rd a ρ
  | .sub Γ A B => ∀ ρ, Fits Rd Γ ρ → cinterp Rd A ρ = cinterp Rd B ρ

/-- A reading **validates** an annotated rule package. -/
structure ReadingValid : Prop where
  /-- Universes are flattened: every universe denotes the universe. -/
  universes : ∀ {h : Head}, R.isUniverse h → Rd.head h = Elem.univ
  /-- A head typed by a head denotes a type, and its type the universe. -/
  headTyping : ∀ {h u : Head}, R.headTyping h u → Rd.head u = Elem.univ ∧ Ty (Rd.head h) Elem.univ
  /-- The join of two universes denotes the universe. -/
  join : ∀ {u v w : Head}, R.isUniverse u → R.isUniverse v → R.join u v w →
    Rd.head w = Elem.univ
  /-- Cumulative heads denote alike. -/
  cumulative : ∀ {u v : Head}, R.cumulative u v → Rd.head u = Rd.head v
  /-- Heads equal by head equality denote alike. -/
  headEq : ∀ {h h' : Head}, R.headEq h h' → Rd.head h = Rd.head h'
  /-- A declared constant denotes an element of its declared type. -/
  constants : ∀ {c : DeclName} {D : CTm Head 0}, P.constantType c = some D →
    TypeGenerated (cinterp Rd D Env.nil) → projT (cinterp Rd D Env.nil) (Rd.const c) = Rd.const c
  /-- A root step relates two terms that denote alike wherever both are elements of one
  type-generated type, with their spine facts there. -/
  roots : ∀ {n : Nat} {l r : CTm Head n} {τ : Ideal} {ρ : Env n}, P.computation.step l r →
    TypeGenerated τ →
    projT τ (cinterp Rd l ρ) = cinterp Rd l ρ → SpineFacts Rd P l τ ρ →
    projT τ (cinterp Rd r ρ) = cinterp Rd r ρ → SpineFacts Rd P r τ ρ →
    cinterp Rd l ρ = cinterp Rd r ρ

/-- **The facts of the domain interpretation** the compatibility lemmas use: the
universes denote the universe, the denotation of a typed term is an element of the
denotation of its type, which is type-generated, and equal terms denote alike. -/
structure SoundnessFacts : Prop where
  universes : ∀ {h : Head}, R.isUniverse h → Rd.head h = Elem.univ
  typing : ∀ {n : Nat} {Γ : CCtx Head n} {t A : CTm Head n}, CTyped P Γ t A →
    ∀ ρ, Fits Rd Γ ρ →
      TypeGenerated (cinterp Rd A ρ) ∧ projT (cinterp Rd A ρ) (cinterp Rd t ρ) = cinterp Rd t ρ
  equality : ∀ {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n}, CEqual P Γ a b A →
    ∀ ρ, Fits Rd Γ ρ → cinterp Rd a ρ = cinterp Rd b ρ

end Definitions

/-! ## Environments and spine facts -/

section Basic

variable {Rd : Reading Head} {P : ChurchRules R}

/-- An environment fitting a context sends each variable to an element of the
denotation of its type, which is type-generated. -/
theorem Fits.lookup : ∀ {n : Nat} {Γ : CCtx Head n} {ρ : Env n}, Fits Rd Γ ρ → ∀ i : Fin n,
    TypeGenerated (cinterp Rd (Γ.lookup i) ρ) ∧ projT (cinterp Rd (Γ.lookup i) ρ) (ρ i) = ρ i
  | _, .nil, _, _, i => i.elim0
  | _, .snoc Γ A, ρ, h, i => by
      obtain ⟨hΓ, hA, h0⟩ := h
      refine Fin.cases ?_ (fun j => ?_) i
      · show TypeGenerated (cinterp Rd (A.rename wk) ρ) ∧
          projT (cinterp Rd (A.rename wk) ρ) (ρ 0) = ρ 0
        rw [cinterp_rename]
        exact ⟨hA, h0⟩
      · show TypeGenerated (cinterp Rd ((Γ.lookup j).rename wk) ρ) ∧
          projT (cinterp Rd ((Γ.lookup j).rename wk) ρ) (ρ j.succ) = ρ j.succ
        rw [cinterp_rename]
        exact Fits.lookup hΓ j

/-- Extending an environment fitting a context by an element of a type-generated
type. -/
theorem Fits.cons {n : Nat} {Γ : CCtx Head n} {A : CTm Head n} {ρ : Env n} {y : Ideal}
    (fits : Fits Rd Γ ρ) (hA : TypeGenerated (cinterp Rd A ρ))
    (hy : projT (cinterp Rd A ρ) y = y) : Fits Rd (.snoc Γ A) (Env.cons y ρ) :=
  ⟨fits, hA, hy⟩

theorem spineFacts_const {n : Nat} {c : DeclName} {τ : Ideal} {ρ : Env n} :
    SpineFacts Rd P (.const c) τ ρ ↔ ∀ D, P.constantType c = some D → τ = cinterp Rd D Env.nil :=
  Iff.rfl

theorem spineFacts_app {n : Nat} {f a : CTm Head n} {τ : Ideal} {ρ : Env n} :
    SpineFacts Rd P (.app f a) τ ρ ↔
      ∃ (T : Ideal) (G : Ideal → Ideal), Cont G ∧ τ = G (cinterp Rd a ρ) ∧
        (projT (cpi T G) (cinterp Rd f ρ) = cinterp Rd f ρ ∧ SpineFacts Rd P f (cpi T G) ρ) ∧
        (projT T (cinterp Rd a ρ) = cinterp Rd a ρ ∧ SpineFacts Rd P a T ρ) :=
  Iff.rfl

theorem spineFacts_refl {n : Nat} {a : CTm Head n} {τ : Ideal} {ρ : Env n} :
    SpineFacts Rd P (.refl a) τ ρ ↔
      ∃ T : Ideal, τ = Ideal.ident T (cinterp Rd a ρ) (cinterp Rd a ρ) ∧
        projT T (cinterp Rd a ρ) = cinterp Rd a ρ ∧ SpineFacts Rd P a T ρ :=
  Iff.rfl

/-- **The spine facts of a spine of a declared constant**: the declared type
instantiated at the arguments is the type, each argument is an element of its
parameter type, and each argument has its spine facts at its parameter type. -/
theorem SpineFacts.constSpine {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) {n : Nat} {ρ : Env n} :
    ∀ {args : List (CTm Head n)} {τ : Ideal},
      SpineFacts Rd P (CTm.appSpine (.const c) args) τ ρ →
        Ideal.SpineFacts (cinterp Rd D Env.nil) (args.map (cinterp Rd · ρ)) τ ∧
        ∀ (as : List (CTm Head n)) (a : CTm Head n) (bs : List (CTm Head n)), args = as ++ a :: bs →
          SpineFacts Rd P a
            (Ideal.dom .pi (instPi (cinterp Rd D Env.nil) (as.map (cinterp Rd · ρ)))) ρ := by
  intro args
  induction args using List.reverseRecOn with
  | nil =>
      intro τ h
      refine ⟨⟨(h D declared).symm, trivial⟩, fun as a bs e => ?_⟩
      exact absurd e.symm (List.append_ne_nil_of_right_ne_nil as (List.cons_ne_nil a bs))
  | append_singleton args x ih =>
      intro τ h
      rw [CTm.appSpine_concat] at h
      obtain ⟨T, G, hG, rfl, ⟨hf, sf⟩, ⟨hx, sx⟩⟩ := spineFacts_app.1 h
      obtain ⟨⟨hinst, hspine⟩, hargs⟩ := ih sf
      obtain ⟨spine', inst'⟩ := Ideal.spine_snoc hG hspine hinst hx
      refine ⟨⟨?_, ?_⟩, fun as a bs e => ?_⟩
      · rw [List.map_append]
        exact inst'
      · rw [List.map_append]
        exact spine'
      · rcases List.eq_nil_or_concat bs with rfl | ⟨L, b, rfl⟩
        · obtain ⟨rfl, e₂⟩ := List.append_inj' e.symm rfl
          obtain ⟨rfl, -⟩ := List.cons.inj e₂
          rw [hinst, Ideal.dom_cpi]
          exact sx
        · have e' : args ++ [x] = (as ++ a :: L) ++ [b] := by
            rw [e, List.concat_eq_append, List.append_assoc, List.cons_append]
          obtain ⟨e₁, -⟩ := List.append_inj' e' rfl
          exact hargs as a L e₁

/-- **Refl facts**: an argument of a spine of a declared constant that is a
reflexivity has as its parameter type an identity type between its point and itself,
of whose carrier the point is an element. -/
theorem SpineFacts.reflArg {c : DeclName} {D : CTm Head 0}
    (declared : P.constantType c = some D) {n : Nat} {ρ : Env n}
    {as bs : List (CTm Head n)} {a : CTm Head n} {τ : Ideal}
    (h : SpineFacts Rd P (CTm.appSpine (.const c) (as ++ .refl a :: bs)) τ ρ) :
    ∃ T : Ideal, Ideal.dom .pi (instPi (cinterp Rd D Env.nil) (as.map (cinterp Rd · ρ))) =
        Ideal.ident T (cinterp Rd a ρ) (cinterp Rd a ρ) ∧
      projT T (cinterp Rd a ρ) = cinterp Rd a ρ := by
  obtain ⟨T, e, ha, -⟩ := spineFacts_refl.1 ((SpineFacts.constSpine declared h).2 as _ bs rfl)
  exact ⟨T, e, ha⟩

end Basic

/-! ## Soundness -/

section Soundness

variable {Rd : Reading Head} {P : ChurchRules R}

/-- A head that denotes the universe is a type-generated type, of which every
type-generated ideal is an element. -/
theorem typed_head_univ {u : Head} (e : Rd.head u = Elem.univ) {n : Nat} {ρ : Env n} {x : Ideal}
    (h : TypeGenerated x) :
    TypeGenerated (cinterp Rd (.head u : CTm Head n) ρ) ∧
      projT (cinterp Rd (.head u : CTm Head n) ρ) x = x := by
  have e' : cinterp Rd (.head u : CTm Head n) ρ = univIdeal := by
    show principal (Rd.head u) = principal Elem.univ
    rw [e]
  rw [e']
  exact ⟨Ideal.typeGenerated_principal Elem.ty_univ_univ, Ideal.projT_univ_eq_self_iff.2 h⟩

/-- An element of the denotation of a universe is type-generated. -/
theorem ReadingValid.typeGenerated_of_head (valid : ReadingValid Rd P) {u : Head}
    (hu : R.isUniverse u) {n : Nat} {ρ : Env n} {x : Ideal}
    (h : projT (cinterp Rd (.head u : CTm Head n) ρ) x = x) : TypeGenerated x := by
  have e' : cinterp Rd (.head u : CTm Head n) ρ = univIdeal := by
    show principal (Rd.head u) = principal Elem.univ
    rw [valid.universes hu]
  rw [e'] at h
  exact Ideal.projT_univ_eq_self_iff.1 h

/-- **Soundness of the annotated calculus**: every derivable statement holds in the
domain, for every reading that validates the rule package. -/
theorem CDerivable.sound (valid : ReadingValid Rd P) {J : CStatement Head}
    (derivation : CDerivable P J) : J.Sound Rd P := by
  induction derivation with
  | @headType n Γ h u typing =>
      intro ρ _
      obtain ⟨hu, hh⟩ := valid.headTyping typing
      obtain ⟨hU, -⟩ := typed_head_univ (n := n) (ρ := ρ) hu (Ideal.typeGenerated_principal hh)
      refine ⟨hU, ?_, trivial⟩
      have e' : cinterp Rd (.head u : CTm Head n) ρ = univIdeal := by
        show principal (Rd.head u) = principal Elem.univ
        rw [hu]
      rw [e']
      exact Ideal.projT_principal_eq (fun _ h => ent_of_mem h) Elem.ty_univ_univ hh
  | @var n Γ i =>
      intro ρ fits
      exact ⟨(fits.lookup i).1, (fits.lookup i).2, trivial⟩
  | @const n Γ name type u declared _ hu ih =>
      intro ρ _
      have hT : TypeGenerated (cinterp Rd type Env.nil) :=
        valid.typeGenerated_of_head hu (ih Env.nil trivial).2.1
      rw [cinterp_liftClosed]
      refine ⟨hT, valid.constants declared hT, fun D hD => ?_⟩
      rw [declared] at hD
      cases hD
      rfl
  | @piForm n Γ A B u v w _ hu _ hv join ihA ihB =>
      intro ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu (ihA ρ fits).2.1
      have hPi : TypeGenerated (cinterp Rd (.pi A B) ρ) :=
        Ideal.typeGenerated_cpi (cinterp_cont_cons Rd B ρ) hA fun y hy =>
          valid.typeGenerated_of_head hv (ihB (Env.cons y ρ) (Fits.cons fits hA hy)).2.1
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.join hu hv join) hPi
      exact ⟨h₁, h₂, trivial⟩
  | @sigmaForm n Γ A B u v w _ hu _ hv join ihA ihB =>
      intro ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu (ihA ρ fits).2.1
      have hS : TypeGenerated (cinterp Rd (.sigma A B) ρ) :=
        Ideal.typeGenerated_csigma (cinterp_cont_cons Rd B ρ) hA fun y hy =>
          valid.typeGenerated_of_head hv (ihB (Env.cons y ρ) (Fits.cons fits hA hy)).2.1
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.join hu hv join) hS
      exact ⟨h₁, h₂, trivial⟩
  | @lamIntro n Γ A body B u w _ hw _ hu _ ihA ihPi ihBody =>
      intro ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hw (ihA ρ fits).2.1
      have hPi : TypeGenerated (cinterp Rd (.pi A B) ρ) :=
        valid.typeGenerated_of_head hu (ihPi ρ fits).2.1
      refine ⟨hPi, ?_, trivial⟩
      exact Ideal.semTyped_clam (cinterp_cont_cons Rd B ρ) (cinterp_cont_cons Rd body ρ)
        fun y hy => (ihBody (Env.cons y ρ) (Fits.cons fits hA hy)).2.1
  | @appElim n Γ g a A B _ _ ihg iha =>
      intro ρ fits
      obtain ⟨hPi, hg, sg⟩ := ihg ρ fits
      obtain ⟨-, ha, sa⟩ := iha ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      rw [cinterp_inst0]
      exact ⟨hPi.cpi_fam hG ha, Ideal.semTyped_app hG hg ha,
        spineFacts_app.2 ⟨cinterp Rd A ρ, fun y => cinterp Rd B (Env.cons y ρ), hG, rfl,
          ⟨hg, sg⟩, ⟨ha, sa⟩⟩⟩
  | @pairIntro n Γ a b A B u _ hu _ _ ihS iha ihb =>
      intro ρ fits
      have hS := valid.typeGenerated_of_head hu (ihS ρ fits).2.1
      obtain ⟨-, ha, -⟩ := iha ρ fits
      obtain ⟨-, hb, -⟩ := ihb ρ fits
      rw [cinterp_inst0] at hb
      exact ⟨hS, Ideal.semTyped_pair (cinterp_cont_cons Rd B ρ) ha hb, trivial⟩
  | @fstElim n Γ p A B _ ihp =>
      intro ρ fits
      obtain ⟨hS, hp, -⟩ := ihp ρ fits
      exact ⟨hS.csigma_dom, Ideal.semTyped_fst (cinterp_cont_cons Rd B ρ) hp, trivial⟩
  | @sndElim n Γ p A B _ ihp =>
      intro ρ fits
      obtain ⟨hS, hp, -⟩ := ihp ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      rw [cinterp_inst0]
      exact ⟨hS.csigma_fam hG (Ideal.semTyped_fst hG hp), Ideal.semTyped_snd hG hp, trivial⟩
  | @idForm n Γ A a b u _ hu _ _ ihA iha ihb =>
      intro ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu (ihA ρ fits).2.1
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.universes hu)
        (Ideal.typeGenerated_ident hA (iha ρ fits).2.1 (ihb ρ fits).2.1)
      exact ⟨h₁, h₂, trivial⟩
  | @reflIntro n Γ a A _ iha =>
      intro ρ fits
      obtain ⟨hA, ha, sa⟩ := iha ρ fits
      exact ⟨Ideal.typeGenerated_ident hA ha ha,
        Ideal.semTyped_refl ha (Ideal.le_refl _) (Ideal.le_refl _),
        spineFacts_refl.2 ⟨cinterp Rd A ρ, rfl, ha, sa⟩⟩
  | @sub n Γ t A B _ _ iht ihle =>
      intro ρ fits
      obtain ⟨hA, ht, st⟩ := iht ρ fits
      rw [← (ihle ρ fits : cinterp Rd A ρ = cinterp Rd B ρ)]
      exact ⟨hA, ht, st⟩
  | @conv n Γ t A B u _ _ _ iht ihE =>
      intro ρ fits
      obtain ⟨hA, ht, st⟩ := iht ρ fits
      rw [← (ihE ρ fits).1]
      exact ⟨hA, ht, st⟩
  | @refl n Γ a A _ iha =>
      intro ρ fits
      obtain ⟨hA, ha, -⟩ := iha ρ fits
      exact ⟨rfl, hA, ha⟩
  | @symm n Γ a b A _ ih =>
      intro ρ fits
      obtain ⟨e, hA, ha⟩ := ih ρ fits
      refine ⟨e.symm, hA, ?_⟩
      rw [← e]
      exact ha
  | @trans n Γ a b c A _ _ ih₁ ih₂ =>
      intro ρ fits
      obtain ⟨e₁, hA, ha⟩ := ih₁ ρ fits
      exact ⟨e₁.trans (ih₂ ρ fits).1, hA, ha⟩
  | @convEq n Γ a b A B u _ _ _ ih ihE =>
      intro ρ fits
      obtain ⟨e, hA, ha⟩ := ih ρ fits
      rw [← (ihE ρ fits).1]
      exact ⟨e, hA, ha⟩
  | @subEq n Γ a b A B _ _ ih ihle =>
      intro ρ fits
      obtain ⟨e, hA, ha⟩ := ih ρ fits
      rw [← (ihle ρ fits : cinterp Rd A ρ = cinterp Rd B ρ)]
      exact ⟨e, hA, ha⟩
  | @headEq n Γ h h' A same _ _ ih _ =>
      intro ρ fits
      obtain ⟨hA, hh, -⟩ := ih ρ fits
      refine ⟨?_, hA, hh⟩
      show principal (Rd.head h) = principal (Rd.head h')
      rw [valid.headEq same]
  | @piCong n Γ A A' B B' u v w _ hu _ hv join ihA ihB =>
      intro ρ fits
      obtain ⟨eA, -, hAu⟩ := ihA ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu hAu
      have hB : ∀ y, projT (cinterp Rd A ρ) y = y →
          cinterp Rd B (Env.cons y ρ) = cinterp Rd B' (Env.cons y ρ) ∧
            TypeGenerated (cinterp Rd B (Env.cons y ρ)) := fun y hy =>
        have h := ihB (Env.cons y ρ) (Fits.cons fits hA hy)
        ⟨h.1, valid.typeGenerated_of_head hv h.2.2⟩
      have hPi : TypeGenerated (cinterp Rd (.pi A B) ρ) :=
        Ideal.typeGenerated_cpi (cinterp_cont_cons Rd B ρ) hA fun y hy => (hB y hy).2
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.join hu hv join) hPi
      refine ⟨?_, h₁, h₂⟩
      show Ideal.cpi (cinterp Rd A ρ) _ = Ideal.cpi (cinterp Rd A' ρ) _
      rw [← eA]
      exact Ideal.cpi_ext fun y hy => (hB y hy).1
  | @sigmaCong n Γ A A' B B' u v w _ hu _ hv join ihA ihB =>
      intro ρ fits
      obtain ⟨eA, -, hAu⟩ := ihA ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu hAu
      have hB : ∀ y, projT (cinterp Rd A ρ) y = y →
          cinterp Rd B (Env.cons y ρ) = cinterp Rd B' (Env.cons y ρ) ∧
            TypeGenerated (cinterp Rd B (Env.cons y ρ)) := fun y hy =>
        have h := ihB (Env.cons y ρ) (Fits.cons fits hA hy)
        ⟨h.1, valid.typeGenerated_of_head hv h.2.2⟩
      have hS : TypeGenerated (cinterp Rd (.sigma A B) ρ) :=
        Ideal.typeGenerated_csigma (cinterp_cont_cons Rd B ρ) hA fun y hy => (hB y hy).2
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.join hu hv join) hS
      refine ⟨?_, h₁, h₂⟩
      show Ideal.csigma (cinterp Rd A ρ) _ = Ideal.csigma (cinterp Rd A' ρ) _
      rw [← eA]
      exact Ideal.csigma_ext fun y hy => (hB y hy).1
  | @idCong n Γ A A' a a' b b' u _ hu _ _ ihA iha ihb =>
      intro ρ fits
      obtain ⟨eA, -, hAu⟩ := ihA ρ fits
      obtain ⟨ea, -, ha⟩ := iha ρ fits
      obtain ⟨eb, -, hb⟩ := ihb ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hu hAu
      obtain ⟨h₁, h₂⟩ := typed_head_univ (n := n) (ρ := ρ) (valid.universes hu)
        (Ideal.typeGenerated_ident hA ha hb)
      refine ⟨?_, h₁, h₂⟩
      show Ideal.ident _ _ _ = Ideal.ident _ _ _
      rw [eA, ea, eb]
  | @lamCong n Γ A A' body body' B u w _ hw _ hu _ ihA ihPi ihBody =>
      intro ρ fits
      obtain ⟨eA, -, hAw⟩ := ihA ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hw hAw
      have hPi : TypeGenerated (cinterp Rd (.pi A B) ρ) :=
        valid.typeGenerated_of_head hu (ihPi ρ fits).2.1
      have hb := fun y (hy : projT (cinterp Rd A ρ) y = y) =>
        ihBody (Env.cons y ρ) (Fits.cons fits hA hy)
      refine ⟨?_, hPi, ?_⟩
      · show Ideal.clam (cinterp Rd A ρ) _ = Ideal.clam (cinterp Rd A' ρ) _
        rw [← eA]
        exact Ideal.clam_ext fun y hy => (hb y hy).1
      · exact Ideal.semTyped_clam (cinterp_cont_cons Rd B ρ) (cinterp_cont_cons Rd body ρ)
          fun y hy => (hb y hy).2.2
  | @appCong n Γ f g a b A B _ _ ihf iha =>
      intro ρ fits
      obtain ⟨ef, hPi, hf⟩ := ihf ρ fits
      obtain ⟨ea, -, ha⟩ := iha ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      refine ⟨?_, ?_, ?_⟩
      · show Ideal.app _ _ = Ideal.app _ _
        rw [ef, ea]
      · rw [cinterp_inst0]
        exact hPi.cpi_fam hG ha
      · rw [cinterp_inst0]
        exact Ideal.semTyped_app hG hf ha
  | @pairCong n Γ a a' b b' A B u _ hu _ _ ihS iha ihb =>
      intro ρ fits
      have hS := valid.typeGenerated_of_head hu (ihS ρ fits).2.1
      obtain ⟨ea, -, ha⟩ := iha ρ fits
      obtain ⟨eb, -, hb⟩ := ihb ρ fits
      rw [cinterp_inst0] at hb
      refine ⟨?_, hS, Ideal.semTyped_pair (cinterp_cont_cons Rd B ρ) ha hb⟩
      show Ideal.pair _ _ = Ideal.pair _ _
      rw [ea, eb]
  | @fstCong n Γ p q A B _ ih =>
      intro ρ fits
      obtain ⟨e, hS, hp⟩ := ih ρ fits
      exact ⟨congrArg Ideal.fst e, hS.csigma_dom,
        Ideal.semTyped_fst (cinterp_cont_cons Rd B ρ) hp⟩
  | @sndCong n Γ p q A B _ ih =>
      intro ρ fits
      obtain ⟨e, hS, hp⟩ := ih ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      rw [cinterp_inst0]
      exact ⟨congrArg Ideal.snd e, hS.csigma_fam hG (Ideal.semTyped_fst hG hp),
        Ideal.semTyped_snd hG hp⟩
  | @reflCong n Γ a b A _ ih =>
      intro ρ fits
      obtain ⟨e, hA, ha⟩ := ih ρ fits
      exact ⟨congrArg Ideal.refl e, Ideal.typeGenerated_ident hA ha ha,
        Ideal.semTyped_refl ha (Ideal.le_refl _) (Ideal.le_refl _)⟩
  | @betaPi n Γ A a body B u _ hu _ _ ihPi ihBody iha =>
      intro ρ fits
      obtain ⟨hA, ha, -⟩ := iha ρ fits
      have hb := ihBody (Env.cons (cinterp Rd a ρ) ρ) (Fits.cons fits hA ha)
      have e : cinterp Rd (.app (.lam A body) a) ρ =
          cinterp Rd body (Env.cons (cinterp Rd a ρ) ρ) := by
        show Ideal.app (cinterp Rd (.lam A body) ρ) (cinterp Rd a ρ) = _
        rw [app_cinterp_lam, ha]
      rw [cinterp_inst0, cinterp_inst0, e]
      exact ⟨rfl, hb.1, hb.2.1⟩
  | @betaFst n Γ A a b B u _ _ _ _ _ iha _ =>
      intro ρ fits
      obtain ⟨hA, ha, -⟩ := iha ρ fits
      have e : cinterp Rd (.fst (.pair a b)) ρ = cinterp Rd a ρ := Ideal.fst_pair _ _
      rw [e]
      exact ⟨rfl, hA, ha⟩
  | @betaSnd n Γ A a b B u _ _ _ _ _ _ ihb =>
      intro ρ fits
      obtain ⟨hB, hb, -⟩ := ihb ρ fits
      have e : cinterp Rd (.snd (.pair a b)) ρ = cinterp Rd b ρ := Ideal.snd_pair _ _
      rw [e]
      exact ⟨rfl, hB, hb⟩
  | @root n Γ l r A _ step _ _ _ _ _ ihl ihr =>
      intro ρ fits
      obtain ⟨hA, hl, sl⟩ := ihl ρ fits
      obtain ⟨-, hr, sr⟩ := ihr ρ fits
      exact ⟨valid.roots step hA hl sl hr sr, hA, hl⟩
  | @etaPi n Γ f g A B _ _ _ ihf ihg ihBody =>
      intro ρ fits
      obtain ⟨hPi, hf, -⟩ := ihf ρ fits
      obtain ⟨-, hg, -⟩ := ihg ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      have hA : TypeGenerated (cinterp Rd A ρ) := hPi.cpi_dom
      refine ⟨?_, hPi, hf⟩
      calc cinterp Rd f ρ = Ideal.clam (cinterp Rd A ρ) (fun y => Ideal.app (cinterp Rd f ρ) y) :=
            (Ideal.clam_app_of_mem hG hf).symm
        _ = Ideal.clam (cinterp Rd A ρ) (fun y => Ideal.app (cinterp Rd g ρ) y) :=
            Ideal.clam_ext fun y hy => by
              have h : Ideal.app (cinterp Rd (f.rename wk) (Env.cons y ρ)) y =
                  Ideal.app (cinterp Rd (g.rename wk) (Env.cons y ρ)) y :=
                (ihBody (Env.cons y ρ) (Fits.cons fits hA hy)).1
              rwa [cinterp_rename_wk, cinterp_rename_wk] at h
        _ = cinterp Rd g ρ := Ideal.clam_app_of_mem hG hg
  | @etaSigma n Γ p q A B _ _ _ _ ihp ihq ihFst ihSnd =>
      intro ρ fits
      obtain ⟨hS, hp, -⟩ := ihp ρ fits
      obtain ⟨-, hq, -⟩ := ihq ρ fits
      have hG := cinterp_cont_cons Rd B ρ
      have e₁ : Ideal.fst (cinterp Rd p ρ) = Ideal.fst (cinterp Rd q ρ) := (ihFst ρ fits).1
      have e₂ : Ideal.snd (cinterp Rd p ρ) = Ideal.snd (cinterp Rd q ρ) := (ihSnd ρ fits).1
      refine ⟨?_, hS, hp⟩
      calc cinterp Rd p ρ = Ideal.pair (Ideal.fst (cinterp Rd p ρ)) (Ideal.snd (cinterp Rd p ρ)) :=
            (Ideal.pair_fst_snd_of_mem hG hp).symm
        _ = Ideal.pair (Ideal.fst (cinterp Rd q ρ)) (Ideal.snd (cinterp Rd q ρ)) := by
            rw [e₁, e₂]
        _ = cinterp Rd q ρ := Ideal.pair_fst_snd_of_mem hG hq
  | @subEqual n Γ A B u _ _ ih =>
      intro ρ fits
      exact (ih ρ fits).1
  | @subUniv n Γ u v c =>
      intro ρ _
      show principal (Rd.head u) = principal (Rd.head v)
      rw [valid.cumulative c]
  | @subPi n Γ A A' B B' u u' w _ _ _ _ _ hw _ _ _ ihA ihB =>
      intro ρ fits
      obtain ⟨eA, -, hAw⟩ := ihA ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) := valid.typeGenerated_of_head hw hAw
      show Ideal.cpi (cinterp Rd A ρ) _ = Ideal.cpi (cinterp Rd A' ρ) _
      rw [← eA]
      exact Ideal.cpi_ext fun y hy => ihB (Env.cons y ρ) (Fits.cons fits hA hy)
  | @subSigma n Γ A A' B B' u u' _ hu _ _ _ _ ihS _ ihA ihB =>
      intro ρ fits
      have hA : TypeGenerated (cinterp Rd A ρ) :=
        (valid.typeGenerated_of_head hu (ihS ρ fits).2.1).csigma_dom
      show Ideal.csigma (cinterp Rd A ρ) _ = Ideal.csigma (cinterp Rd A' ρ) _
      rw [← (ihA ρ fits : cinterp Rd A ρ = cinterp Rd A' ρ)]
      exact Ideal.csigma_ext fun y hy => ihB (Env.cons y ρ) (Fits.cons fits hA hy)
  | @subTrans n Γ A B C _ _ ih₁ ih₂ =>
      intro ρ fits
      exact (ih₁ ρ fits : cinterp Rd A ρ = cinterp Rd B ρ).trans (ih₂ ρ fits)

/-- **Typing soundness.** -/
theorem CTyped.sound (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n} {t A : CTm Head n}
    (typing : CTyped P Γ t A) {ρ : Env n} (fits : Fits Rd Γ ρ) :
    TypeGenerated (cinterp Rd A ρ) ∧ projT (cinterp Rd A ρ) (cinterp Rd t ρ) = cinterp Rd t ρ ∧
      SpineFacts Rd P t (cinterp Rd A ρ) ρ :=
  CDerivable.sound valid typing ρ fits

/-- **Equality soundness.** -/
theorem CEqual.sound (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n} {a b A : CTm Head n}
    (equal : CEqual P Γ a b A) {ρ : Env n} (fits : Fits Rd Γ ρ) :
    cinterp Rd a ρ = cinterp Rd b ρ :=
  (CDerivable.sound valid equal ρ fits).1

/-- **Subtyping soundness**: subtyping is interpreted by equality. -/
theorem CBelow.sound (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (below : CBelow P Γ A B) {ρ : Env n} (fits : Fits Rd Γ ρ) :
    cinterp Rd A ρ = cinterp Rd B ρ :=
  CDerivable.sound valid below ρ fits

/-- Subtyping is interpreted by an inclusion. -/
theorem CBelow.sound_le (valid : ReadingValid Rd P) {n : Nat} {Γ : CCtx Head n}
    {A B : CTm Head n} (below : CBelow P Γ A B) {ρ : Env n} (fits : Fits Rd Γ ρ) :
    cinterp Rd A ρ ≤ cinterp Rd B ρ :=
  (CBelow.sound valid below fits) ▸ Ideal.le_refl _

/-- **The soundness facts hold for every valid reading.** -/
theorem ReadingValid.soundnessFacts (valid : ReadingValid Rd P) : SoundnessFacts Rd P where
  universes := valid.universes
  typing := fun typing _ fits => ⟨(CTyped.sound valid typing fits).1,
    (CTyped.sound valid typing fits).2.1⟩
  equality := fun equal _ fits => CEqual.sound valid equal fits

end Soundness

/-! ## Readings of packages with a level model -/

/-- **A reading validates a rule package with a level model** when universes denote
the universe, heads denote types, head equality is respected, constants denote
elements of their declared types, and root steps are valid. -/
theorem ReadingValid.ofLevels {Rd : Reading Head} {P : ChurchRules R} {L : Type}
    [LevelOrder L] (levels : LevelModel R L)
    (universes : ∀ {h : Head}, R.isUniverse h → Rd.head h = Elem.univ)
    (heads : ∀ h : Head, Ty (Rd.head h) Elem.univ)
    (headEq : ∀ {h h' : Head}, R.headEq h h' → Rd.head h = Rd.head h')
    (constants : ∀ {c : DeclName} {D : CTm Head 0}, P.constantType c = some D →
      TypeGenerated (cinterp Rd D Env.nil) → projT (cinterp Rd D Env.nil) (Rd.const c) = Rd.const c)
    (roots : ∀ {n : Nat} {l r : CTm Head n} {τ : Ideal} {ρ : Env n}, P.computation.step l r →
      TypeGenerated τ →
      projT τ (cinterp Rd l ρ) = cinterp Rd l ρ → SpineFacts Rd P l τ ρ →
      projT τ (cinterp Rd r ρ) = cinterp Rd r ρ → SpineFacts Rd P r τ ρ →
      cinterp Rd l ρ = cinterp Rd r ρ) :
    ReadingValid Rd P where
  universes := universes
  headTyping := fun typing => ⟨universes (levels.ground_typing typing), heads _⟩
  join := fun _ _ join => universes (levels.join_level join).1
  cumulative := fun c =>
    (universes (levels.cumulative_universe c).1).trans
      (universes (levels.cumulative_universe c).2.1).symm
  headEq := headEq
  constants := constants
  roots := roots

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
