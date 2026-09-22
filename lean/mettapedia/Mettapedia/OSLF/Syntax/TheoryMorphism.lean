import Mettapedia.OSLF.Syntax.SignatureMorphism

/-!
# Positioned-rule morphisms and modality transport

Section 19.8 of Finding Mind says the construction is functorial: on a morphism
of theories the action is by transport,

    <K_j>_{x :: A} B  |-->  <F(K_j)>_{x :: F(A)} (F . B),    <>B  |-->  <>(F . B),

with morphisms required to preserve the rewrite relation and the internal
language structure. `SignatureMorphism` carries a chosen linear context and
its carrier. This module proves transport and composition laws for the scoped,
unconditional positioned-rule fragment with explicit instance maps. It does
not construct the chapter-19 generated typing, free extension or generator
functor, nor supply conditional-premise transport or equations compatibility.
Within this fragment, relational transport splits.

The **existential** modalities do transport.  Possibility, and the modality at a
chosen position, are built from an instance the rule is free to choose, and so
an instance upstream supplies one downstream, with `F . B` the direct image.

The **rely-indexed** modality does not.  Its universal quantifier ranges over
assignments to the rule's rely parameters and therefore points the wrong way
through the morphism: an assignment downstream has to be pulled back before the
upstream specification can be used, and values travel along a change of
signature in the forward direction only.  The extra datum needed is isolated
here as an environment covering, transport is proved under it, and a concrete
pair of theories is exhibited where no covering exists and the transport fails.

The obstruction is that a change of signature need not be surjective on closed
terms at a rely sort.  Collapsing sorts creates downstream values that are the
image of nothing upstream; the downstream universal quantifier ranges over them,
and the upstream specification has never been asked about them.  Inhabitation
has nothing to do with it: a variable at an uninhabited sort that the rule does
*not* rely on is invisible to the modality, and this module proves that too --
correcting an earlier claim of this file, which read non-transport off exactly
that vacuity and was an artifact of indexing the modality by closing
substitutions of the whole variable context rather than by the reliance set.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S T : Signature}

/-- Move a term along an equality of sorts. -/
def castTermSort {T : Signature} {Γ : Ctx T} {s s' : T.Srt} (h : s = s')
    (t : Term T Γ s) : Term T Γ s' := h ▸ t

theorem castTermSort_trans {T : Signature} {Γ : Ctx T} {s s' s'' : T.Srt}
    (h : s = s') (h' : s' = s'') (t : Term T Γ s) :
    castTermSort h' (castTermSort h t) = castTermSort (h.trans h') t := by
  subst h
  subst h'
  rfl

theorem mapTerm_castTermSort (F : SigMor S T) {Γ : Ctx S} {Δ : Ctx T}
    (ν : VarMap F.sortMap Γ Δ) {s s' : S.Srt} (h : s = s') (t : Term S Γ s) :
    mapTerm F ν (castTermSort h t) =
      castTermSort (congrArg F.sortMap h) (mapTerm F ν t) := by
  subst h
  rfl

/-- The existing identity action specializes to closed terms without a context cast. -/
theorem SigMor.onClosedTerm_ident {s : S.Srt} (t : Term S [] s) :
    (SigMor.ident S).onTerm t = t := by
  change mapTerm (SigMor.ident S) (mapVar (fun s : S.Srt => s)) t = t
  rw [mapTerm_ident]
  have hν : mapVar (fun s : S.Srt => s) (Γ := []) = (fun _ x => x) := by
    funext s x
    cases x
  rw [hν, rename_id]

/-- The existing compositional action specializes to closed contexts. -/
theorem SigMor.onClosedTerm_comp {U : Signature} (F : SigMor S T) (G : SigMor T U)
    {s : S.Srt} (t : Term S [] s) :
    G.onTerm (F.onTerm t) = (F.comp G).onTerm t := by
  change mapTerm G (mapVar G.sortMap) (mapTerm F (mapVar F.sortMap) t) =
    mapTerm (F.comp G) (mapVar (F.comp G).sortMap) t
  rw [mapTerm_comp]
  apply mapTerm_congr
  intro s x
  cases x

theorem SigMor.onClosedTerm_castSort (F : SigMor S T) {s s' : S.Srt}
    (h : s = s') (t : Term S [] s) :
    F.onTerm (castTermSort h t) =
      castTermSort (congrArg F.sortMap h) (F.onTerm t) :=
  mapTerm_castTermSort F (mapVar F.sortMap) h t

/-- A **morphism of positioned-rewrite theories**: a change of signature, a
matching of the rule's sort and of its position's carrier, and a map on rule
instances under which both sides and the chosen redex are carried across.

The instance map is what "preserves the rewrite relation" amounts to
operationally: a firing upstream is a firing downstream, with the same
decomposition. -/
structure RewriteMor {M : List (MetaArity S)} {N : List (MetaArity T)}
    (P : PositionedRewrite (withMetas S M)) (Q : PositionedRewrite (withMetas T N)) where
  /-- The change of signature. -/
  sig : SigMor S T
  /-- The rules have corresponding sorts. -/
  onSort : sig.sortMap P.sort = Q.sort
  /-- The positions have corresponding carriers. -/
  onCarrier : sig.sortMap P.position.carrier = Q.position.carrier
  /-- Every firing upstream names a firing downstream. -/
  onInstance : RuleInstance M P → RuleInstance N Q
  /-- ... with the translated left-hand side. -/
  lhs_ok : ∀ I : RuleInstance M P,
    bind (onInstance I).close (instantiate (onInstance I).body Q.lhs)
      = castTermSort onSort (sig.onTerm (bind I.close (instantiate I.body P.lhs)))
  /-- ... the translated right-hand side. -/
  rhs_ok : ∀ I : RuleInstance M P,
    bind (onInstance I).close (instantiate (onInstance I).body Q.rhs)
      = castTermSort onSort (sig.onTerm (bind I.close (instantiate I.body P.rhs)))
  /-- ... and the translated redex at the chosen position. -/
  redex_ok : ∀ I : RuleInstance M P,
    bind (onInstance I).close (instantiate (onInstance I).body Q.position.redex)
      = castTermSort onCarrier
          (sig.onTerm (bind I.close (instantiate I.body P.position.redex)))

namespace RewriteMor

variable {M : List (MetaArity S)} {N : List (MetaArity T)}
  {P : PositionedRewrite (withMetas S M)} {Q : PositionedRewrite (withMetas T N)}

/-- A positioned-rule morphism is determined by its signature and instance maps. -/
@[ext] theorem ext (Φ Ψ : RewriteMor P Q) (hsig : Φ.sig = Ψ.sig)
    (hinstance : ∀ I, Φ.onInstance I = Ψ.onInstance I) : Φ = Ψ := by
  cases Φ
  cases Ψ
  cases hsig
  have hmap := funext hinstance
  cases hmap
  rfl

/-- Identity transport retains the actual rule instance. -/
def ident (P : PositionedRewrite (withMetas S M)) : RewriteMor P P where
  sig := SigMor.ident S
  onSort := rfl
  onCarrier := rfl
  onInstance := fun I => I
  lhs_ok := fun I => (SigMor.onClosedTerm_ident
    (bind I.close (instantiate I.body P.lhs))).symm
  rhs_ok := fun I => (SigMor.onClosedTerm_ident
    (bind I.close (instantiate I.body P.rhs))).symm
  redex_ok := fun I => (SigMor.onClosedTerm_ident
    (bind I.close (instantiate I.body P.position.redex))).symm

/-- Compose the actual instance maps and derive compatibility from signature transport. -/
def comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) : RewriteMor P R where
  sig := Φ.sig.comp Ψ.sig
  onSort := (congrArg Ψ.sig.sortMap Φ.onSort).trans Ψ.onSort
  onCarrier := (congrArg Ψ.sig.sortMap Φ.onCarrier).trans Ψ.onCarrier
  onInstance := fun I => Ψ.onInstance (Φ.onInstance I)
  lhs_ok := by
    intro I
    rw [Ψ.lhs_ok, Φ.lhs_ok, SigMor.onClosedTerm_castSort,
      castTermSort_trans, SigMor.onClosedTerm_comp]
  rhs_ok := by
    intro I
    rw [Ψ.rhs_ok, Φ.rhs_ok, SigMor.onClosedTerm_castSort,
      castTermSort_trans, SigMor.onClosedTerm_comp]
  redex_ok := by
    intro I
    rw [Ψ.redex_ok, Φ.redex_ok, SigMor.onClosedTerm_castSort,
      castTermSort_trans, SigMor.onClosedTerm_comp]

@[simp] theorem ident_onInstance (I : RuleInstance M P) :
    (ident P).onInstance I = I := rfl

@[simp] theorem comp_onInstance {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) (I : RuleInstance M P) :
    (Φ.comp Ψ).onInstance I = Ψ.onInstance (Φ.onInstance I) := rfl

@[simp] theorem ident_comp (Φ : RewriteMor P Q) : (ident P).comp Φ = Φ := by
  apply ext
  · rfl
  · intro I
    rfl

@[simp] theorem comp_ident (Φ : RewriteMor P Q) : Φ.comp (ident Q) = Φ := by
  apply ext
  · rfl
  · intro I
    rfl

theorem comp_assoc {U V : Signature} {O : List (MetaArity U)}
    {K : List (MetaArity V)} {R : PositionedRewrite (withMetas U O)}
    {W : PositionedRewrite (withMetas V K)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) (Χ : RewriteMor R W) :
    (Φ.comp Ψ).comp Χ = Φ.comp (Ψ.comp Χ) := by
  apply ext
  · rfl
  · intro I
    rfl

/-- The action on closed terms at the rule's sort. -/
def img (Φ : RewriteMor P Q) (t : Term S [] P.sort) : Term T [] Q.sort :=
  castTermSort Φ.onSort (Φ.sig.onTerm t)

/-- The action on closed terms at the position's carrier. -/
def imgCarrier (Φ : RewriteMor P Q) (t : Term S [] P.position.carrier) :
    Term T [] Q.position.carrier :=
  castTermSort Φ.onCarrier (Φ.sig.onTerm t)

/-- `F . B`: the direct image of a predicate. -/
def imgPred (Φ : RewriteMor P Q) (B : Term S [] P.sort → Prop) :
    Term T [] Q.sort → Prop :=
  fun v => ∃ w, B w ∧ v = Φ.img w

@[simp] theorem img_ident (t : Term S [] P.sort) : (ident P).img t = t := by
  simp only [img, ident, SigMor.onClosedTerm_ident, castTermSort]

@[simp] theorem imgCarrier_ident (t : Term S [] P.position.carrier) :
    (ident P).imgCarrier t = t := by
  simp only [imgCarrier, ident, SigMor.onClosedTerm_ident, castTermSort]

@[simp] theorem img_comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) (t : Term S [] P.sort) :
    (Φ.comp Ψ).img t = Ψ.img (Φ.img t) := by
  simp only [img, comp, SigMor.onClosedTerm_castSort, castTermSort_trans,
    SigMor.onClosedTerm_comp]

@[simp] theorem imgCarrier_comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) (t : Term S [] P.position.carrier) :
    (Φ.comp Ψ).imgCarrier t = Ψ.imgCarrier (Φ.imgCarrier t) := by
  simp only [imgCarrier, comp, SigMor.onClosedTerm_castSort, castTermSort_trans,
    SigMor.onClosedTerm_comp]

@[simp] theorem imgPred_ident (B : Term S [] P.sort → Prop) :
    (ident P).imgPred B = B := by
  funext v
  apply propext
  constructor
  · rintro ⟨w, hB, hv⟩
    rw [hv, img_ident]
    exact hB
  · intro hB
    exact ⟨v, hB, (img_ident v).symm⟩

/-- Direct image composes along the same instance and term transport. -/
@[simp] theorem imgPred_comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)} (Φ : RewriteMor P Q)
    (Ψ : RewriteMor Q R) (B : Term S [] P.sort → Prop) :
    (Φ.comp Ψ).imgPred B = Ψ.imgPred (Φ.imgPred B) := by
  funext v
  apply propext
  constructor
  · rintro ⟨w, hB, hv⟩
    exact ⟨Φ.img w, ⟨w, hB, rfl⟩, by simpa only [img_comp] using hv⟩
  · rintro ⟨u, ⟨w, hB, hu⟩, hv⟩
    refine ⟨w, hB, ?_⟩
    rw [img_comp, ← hu]
    exact hv

/-- **The generated relation travels.** -/
theorem rootStep_transport (Φ : RewriteMor P Q) {t u : Term S [] P.sort}
    (h : RootStep P t u) : RootStep Q (Φ.img t) (Φ.img u) := by
  obtain ⟨I, hl, hr⟩ := h
  exact ⟨Φ.onInstance I, by rw [Φ.lhs_ok I, hl]; rfl, by rw [Φ.rhs_ok I, hr]; rfl⟩

/-- **`<>B |--> <>(F . B)`.** -/
theorem poss_transport (Φ : RewriteMor P Q) {B : Term S [] P.sort → Prop}
    {t : Term S [] P.sort} (h : Poss P B t) : Poss Q (Φ.imgPred B) (Φ.img t) := by
  obtain ⟨u, hstep, hB⟩ := h
  exact ⟨Φ.img u, Φ.rootStep_transport hstep, u, hB, rfl⟩

/-- **The modality at a chosen position travels**, in its unindexed form:
`<K>B |--> <F K>(F . B)`.  Both quantifiers are existential, so an instance
upstream is enough. -/
theorem stepsFromPosition_transport (Φ : RewriteMor P Q)
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : StepsFromPosition P B t) :
    StepsFromPosition Q (Φ.imgPred B) (Φ.imgCarrier t) := by
  obtain ⟨I, ht, hB⟩ := h
  refine ⟨Φ.onInstance I, ?_, ?_⟩
  · rw [Φ.redex_ok I, ht]; rfl
  · rw [Φ.rhs_ok I]
    exact ⟨_, hB, rfl⟩

/-- The datum the rely-indexed transport needs and the morphism does not carry:
every downstream environment admissible for the transported assumptions comes
from an upstream one admissible for the original assumptions, and the instance
map keeps the agreement. -/
structure EnvCovering (Φ : RewriteMor P Q) (A : RelyTyping P) (A' : RelyTyping Q) where
  /-- Pull an admissible downstream rely environment back. -/
  lift : ∀ env' : RelyEnv Q,
    (∀ (s : T.Srt) (y : Var Q.ctx s) (hy : Q.RelyParameter y), A' s y (env' s y hy)) →
    RelyEnv P
  /-- The pullback is admissible upstream. -/
  lift_ok : ∀ env' h, ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x),
    A s x (lift env' h s x hx)
  /-- An instance realising the pullback maps to one realising the original. -/
  agree : ∀ env' h (I : RuleInstance M P), Realises P I.close (lift env' h) →
    Realises Q (Φ.onInstance I).close env'

namespace EnvCovering

/-- A covering is determined by its pullback of admissible environments;
the admissibility and instance-agreement fields are proof-valued. -/
@[ext] theorem ext {Φ : RewriteMor P Q} {A : RelyTyping P} {A' : RelyTyping Q}
    (C D : EnvCovering Φ A A')
    (lifts : ∀ env h, C.lift env h = D.lift env h) : C = D := by
  cases C
  cases D
  have same := funext (fun env => funext (lifts env))
  cases same
  rfl

/-- Identity covering keeps the actual rely environment and its assumptions. -/
def ident (P : PositionedRewrite (withMetas S M)) (A : RelyTyping P) :
    EnvCovering (RewriteMor.ident P) A A where
  lift env _ := env
  lift_ok _ h := h
  agree _ _ _ h := h

/-- Coverings compose contravariantly on environments and covariantly on
the same retained rule instances. No surjectivity is inferred from a
signature map. -/
def comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)}
    {Φ : RewriteMor P Q} {Ψ : RewriteMor Q R}
    {A : RelyTyping P} {A' : RelyTyping Q} {A'' : RelyTyping R}
    (C : EnvCovering Φ A A') (D : EnvCovering Ψ A' A'') :
    EnvCovering (Φ.comp Ψ) A A'' where
  lift env h := C.lift (D.lift env h) (D.lift_ok env h)
  lift_ok env h := C.lift_ok (D.lift env h) (D.lift_ok env h)
  agree env h I realized :=
    D.agree env h (Φ.onInstance I)
      (C.agree (D.lift env h) (D.lift_ok env h) I realized)

@[simp] theorem ident_lift (A : RelyTyping P) (env : RelyEnv P)
    (h : ∀ s x hx, A s x (env s x hx)) :
    (ident P A).lift env h = env := rfl

@[simp] theorem comp_lift {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)}
    {Φ : RewriteMor P Q} {Ψ : RewriteMor Q R}
    {A : RelyTyping P} {A' : RelyTyping Q} {A'' : RelyTyping R}
    (C : EnvCovering Φ A A') (D : EnvCovering Ψ A' A'') (env : RelyEnv R)
    (h : ∀ s x hx, A'' s x (env s x hx)) :
    (C.comp D).lift env h = C.lift (D.lift env h) (D.lift_ok env h) := rfl

@[simp] theorem ident_comp {Φ : RewriteMor P Q}
    {A : RelyTyping P} {A' : RelyTyping Q} (C : EnvCovering Φ A A') :
    (ident P A).comp C = C := by
  apply ext
  intro env h
  rfl

@[simp] theorem comp_ident {Φ : RewriteMor P Q}
    {A : RelyTyping P} {A' : RelyTyping Q} (C : EnvCovering Φ A A') :
    C.comp (ident Q A') = C := by
  apply ext
  intro env h
  rfl

/-- Admissible environment pullbacks associate along the same three
positioned-rule maps. -/
theorem comp_assoc {U V : Signature} {O : List (MetaArity U)} {K : List (MetaArity V)}
    {R : PositionedRewrite (withMetas U O)} {W : PositionedRewrite (withMetas V K)}
    {Φ : RewriteMor P Q} {Ψ : RewriteMor Q R} {Χ : RewriteMor R W}
    {A : RelyTyping P} {A' : RelyTyping Q} {A'' : RelyTyping R} {A''' : RelyTyping W}
    (C : EnvCovering Φ A A') (D : EnvCovering Ψ A' A'') (E : EnvCovering Χ A'' A''') :
    (C.comp D).comp E = C.comp (D.comp E) := by
  apply ext
  intro env h
  rfl

end EnvCovering

/-- **The rely-indexed modality travels once the covering is supplied** -- and
only then.  This is the corrected form of the transport formula for the indexed
modality. -/
theorem relyPossibly_transport (Φ : RewriteMor P Q) {A : RelyTyping P} {A' : RelyTyping Q}
    (C : EnvCovering Φ A A') {B : Term S [] P.sort → Prop}
    {t : Term S [] P.position.carrier} (h : RelyPossibly P A B t) :
    RelyPossibly Q A' (Φ.imgPred B) (Φ.imgCarrier t) := by
  intro env' henv'
  obtain ⟨I, hag, ht, hB⟩ := h (C.lift env' henv') (C.lift_ok env' henv')
  refine ⟨Φ.onInstance I, C.agree env' henv' I hag, ?_, ?_⟩
  · rw [Φ.redex_ok I, ht]; rfl
  · rw [Φ.rhs_ok I]
    exact ⟨_, hB, rfl⟩

/-- Indexed transport through two theories uses the composed covering,
instance maps, and predicate images rather than a new semantic relation. -/
theorem relyPossibly_transport_comp {U : Signature} {O : List (MetaArity U)}
    {R : PositionedRewrite (withMetas U O)}
    (Φ : RewriteMor P Q) (Ψ : RewriteMor Q R)
    {A : RelyTyping P} {A' : RelyTyping Q} {A'' : RelyTyping R}
    (C : EnvCovering Φ A A') (D : EnvCovering Ψ A' A'')
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : RelyPossibly P A B t) :
    RelyPossibly R A'' (Ψ.imgPred (Φ.imgPred B))
      (Ψ.imgCarrier (Φ.imgCarrier t)) := by
  simpa only [imgPred_comp, imgCarrier_comp] using
    relyPossibly_transport (Φ.comp Ψ) (C.comp D) h

end RewriteMor

/-! ## An uninhabited sort off the reliance set is invisible

This namespace carries a correction.  It was built to argue that a morphism can
satisfy every condition the source imposes and still fail to carry the
rely-indexed modality, on the grounds that the upstream rule's context contains
a sort with no closed terms, so the upstream specification holds for want of an
environment to test it against.

That argument was wrong, and the theorems below say why.  The modality is
indexed by the rule's reliance set; the uninhabited sort here sits at a variable
which is neither a rely nor a local parameter, so no rely environment mentions
it, rely environments exist, and the upstream specification is *not* vacuous.
It is simply false: the rule has no instances, so nothing can witness the
existential.  The construction is kept, with its claim inverted, because the
correction is the content -- vacuity by uninhabitation was an artifact of
quantifying over closing substitutions of the whole variable context instead of
over the reliance set.

The real obstruction to transport is proved further down, over a morphism whose
rule fires. -/

namespace NoCovering

inductive Srt3 where
  | nm
  | pr
  /-- A sort with no operators: nothing closed inhabits it. -/
  | gh
  deriving DecidableEq

inductive Op3 : Srt3 → Type where
  | aName : Op3 Srt3.nm
  | nil : Op3 Srt3.pr
  | out : Op3 Srt3.pr

abbrev sig3 : Signature where
  Srt := Srt3
  Op := Op3
  arity := fun {_} o => match o with
    | .aName => []
    | .nil => []
    | .out => [([], Srt3.nm), ([], Srt3.pr)]

inductive OneSrt3 where
  | all
  deriving DecidableEq

inductive OneOp3 : OneSrt3 → Type where
  | aName : OneOp3 OneSrt3.all
  | nil : OneOp3 OneSrt3.all
  | out : OneOp3 OneSrt3.all

abbrev osig3 : Signature where
  Srt := OneSrt3
  Op := OneOp3
  arity := fun {_} o => match o with
    | .aName => []
    | .nil => []
    | .out => [([], OneSrt3.all), ([], OneSrt3.all)]

/-- Collapse the three sorts to one. -/
def collapse3 : SigMor sig3 osig3 where
  sortMap := fun _ => OneSrt3.all
  opMap := fun {_} o => match o with
    | .aName => OneOp3.aName
    | .nil => OneOp3.nil
    | .out => OneOp3.out
  carriesArity := by
    intro _ o
    cases o <;> rfl

/-- **Upstream, one sort is uninhabited by closed terms.** -/
theorem no_closed_gh (t : Term sig3 [] Srt3.gh) : False := by
  cases t with
  | var v => cases v
  | op o _ => cases o

/-- **Downstream, every sort is inhabited.** -/
def nilO : Term osig3 [] OneSrt3.all := Term.op (S := osig3) OneOp3.nil Args.nil

def nilS : Term sig3 [] Srt3.pr := Term.op (S := sig3) Op3.nil Args.nil

abbrev SM3 : Signature := withMetas sig3 []
abbrev OM3 : Signature := withMetas osig3 []

/-- The rule's variables: a ghost, a name, a process. -/
abbrev G3 : Ctx SM3 := [Srt3.gh, Srt3.nm, Srt3.pr]

abbrev H3 : Ctx OM3 := [OneSrt3.all, OneSrt3.all, OneSrt3.all]

/-- `out(n, p)`, which never mentions the ghost. -/
def lhs3 : Term SM3 G3 Srt3.pr :=
  Term.op (S := SM3) (Sum.inl Op3.out)
    (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))

/-- `out([], p)`: the hole is at the name. -/
def ctxt3 : Term SM3 (Srt3.nm :: G3) Srt3.pr :=
  Term.op (S := SM3) (Sum.inl Op3.out)
    (.cons (.var .zero) (.cons (.var (.succ (.succ (.succ .zero)))) .nil))

/-- The upstream rule `out(n, p) ~> p`, with the name occurrence chosen. -/
def P3 : PositionedRewrite SM3 where
  ctx := G3
  sort := Srt3.pr
  lhs := lhs3
  rhs := .var (.succ (.succ .zero))
  position :=
    { carrier := Srt3.nm
      ctxt := ctxt3
      redex := .var (.succ .zero)
      plugs := rfl
      linear := rfl }

def olhs3 : Term OM3 H3 OneSrt3.all :=
  Term.op (S := OM3) (Sum.inl OneOp3.out)
    (.cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) .nil))

def octxt3 : Term OM3 (OneSrt3.all :: H3) OneSrt3.all :=
  Term.op (S := OM3) (Sum.inl OneOp3.out)
    (.cons (.var .zero) (.cons (.var (.succ (.succ (.succ .zero)))) .nil))

/-- The same rule downstream, with the sorts collapsed. -/
def Q3 : PositionedRewrite OM3 where
  ctx := H3
  sort := OneSrt3.all
  lhs := olhs3
  rhs := .var (.succ (.succ .zero))
  position :=
    { carrier := OneSrt3.all
      ctxt := octxt3
      redex := .var (.succ .zero)
      plugs := rfl
      linear := rfl }

/-- The morphism.  Every condition holds -- there is nothing upstream for them
to constrain, because the rule has no instances at all. -/
def Phi3 : RewriteMor P3 Q3 where
  sig := collapse3
  onSort := rfl
  onCarrier := rfl
  onInstance := fun I => (no_closed_gh (I.close Srt3.gh Var.zero)).elim
  lhs_ok := fun I => (no_closed_gh (I.close Srt3.gh Var.zero)).elim
  rhs_ok := fun I => (no_closed_gh (I.close Srt3.gh Var.zero)).elim
  redex_ok := fun I => (no_closed_gh (I.close Srt3.gh Var.zero)).elim

/-- No assumptions upstream. -/
def Aup : RelyTyping P3 := fun _ _ _ => True

/-- Downstream, the direct image: a value must come from a closed upstream
process.  Those exist, so this is a real condition that real environments meet. -/
def Adown : RelyTyping Q3 := fun s => match s with
  | OneSrt3.all => fun _ v => ∃ w : Term sig3 [] Srt3.pr, v = collapse3.onTerm w

/-- The target predicate, which nothing satisfies. -/
def Bfalse : Term sig3 [] P3.sort → Prop := fun _ => False

/-- A closed term at the position's carrier. -/
def t3 : Term sig3 [] Srt3.nm := Term.op (S := sig3) Op3.aName Args.nil

/-- A downstream environment. -/
def env3 : Sub osig3 Q3.ctx [] := fun s => match s with
  | OneSrt3.all => fun _ => nilO

/-- ... which meets the transported assumptions, and does so honestly: `nilO`
really is the image of a closed upstream process. -/
theorem env3_admissible :
    ∀ (s : OneSrt3) (y : Var Q3.ctx s) (hy : Q3.RelyParameter y),
      Adown s y (relyEnvOf env3 s y hy)
  | OneSrt3.all, _, _ => ⟨nilS, rfl⟩

/-- **The ghost variable is not a rely parameter**: the one-hole context does
not mention it.  So no rely environment is ever asked for a term at its sort,
and the sort's uninhabitation is invisible to the modality. -/
theorem gh_not_rely : ¬ P3.RelyParameter (Var.zero : Var G3 Srt3.gh) := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- **Rely environments for the upstream rule exist**, uninhabited sort and
all: the reliance set is the continuation alone, and processes are inhabited. -/
def env3up : (s : Srt3) → (x : Var G3 s) → P3.RelyParameter x → Term sig3 [] s
  | _, .zero, hx => absurd hx gh_not_rely
  | _, .succ .zero, _ => t3
  | _, .succ (.succ .zero), _ => nilS
  | _, .succ (.succ (.succ v)), _ => nomatch v

/-- **Retraction, stated as a theorem.**  An earlier version of this file
claimed the upstream specification held here, vacuously, for want of an
environment.  Indexed by the reliance set it does not hold at all: a rely
environment exists, so the existential has to be met, and it cannot be, because
the rule has no instances.  Vacuity by uninhabitation was an artifact of the
index, not a fact about the theory. -/
theorem source_does_not_hold : ¬ RelyPossibly P3 Aup Bfalse t3 := by
  intro h
  obtain ⟨I, -, -, -⟩ := h env3up (fun _ _ _ => trivial)
  exact no_closed_gh (I.close Srt3.gh Var.zero)

/-- Downstream the specification fails too, so this pair witnesses nothing about
transport: both sides are false. -/
theorem target_fails :
    ¬ RelyPossibly Q3 Adown (Phi3.imgPred Bfalse) (Phi3.imgCarrier t3) := by
  intro h
  obtain ⟨_J, _hag, _ht, hB⟩ := h (relyEnvOf env3) env3_admissible
  obtain ⟨_w, hw, _⟩ := hB
  exact hw

/-- **Both sides are false, so nothing here separates them.**  This is the
withdrawn claim in its accurate form. -/
theorem neither_side_holds :
    ¬ RelyPossibly P3 Aup Bfalse t3
      ∧ ¬ RelyPossibly Q3 Adown (Phi3.imgPred Bfalse) (Phi3.imgCarrier t3) :=
  ⟨source_does_not_hold, target_fails⟩

/-- The positive half is unaffected: the existential modalities still travel,
and here they do so trivially because nothing fires. -/
theorem poss_still_transports {B : Term sig3 [] P3.sort → Prop}
    {t : Term sig3 [] P3.sort} (h : Poss P3 B t) :
    Poss Q3 (Phi3.imgPred B) (Phi3.img t) :=
  Phi3.poss_transport h

end NoCovering

/-! ## A theory morphism that carries something

The counterexample above is deliberately degenerate: its upstream rule fires
nowhere, which is how it satisfies every condition while transporting nothing.
So the transport theorems need a witness that is not.  Here is one -- the same
sort collapse, applied to a rule whose context has no uninhabited sort, so the
rule has instances, fires, and its firing arrives downstream.  The environment
covering exists here, and the rely-indexed modality transports along it. -/

namespace Collapsing

open NoCovering

/-- A rule context with no uninhabited sort. -/
abbrev K4 : Ctx SM3 := [Srt3.nm, Srt3.pr]

abbrev L4 : Ctx OM3 := [OneSrt3.all, OneSrt3.all]

def lhs4 : Term SM3 K4 Srt3.pr :=
  Term.op (S := SM3) (Sum.inl Op3.out)
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

def ctxt4 : Term SM3 (Srt3.nm :: K4) Srt3.pr :=
  Term.op (S := SM3) (Sum.inl Op3.out)
    (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil))

/-- `out(n, p) ~> p`, with the name occurrence chosen. -/
def P4 : PositionedRewrite SM3 where
  ctx := K4
  sort := Srt3.pr
  lhs := lhs4
  rhs := .var (.succ .zero)
  position :=
    { carrier := Srt3.nm
      ctxt := ctxt4
      redex := .var .zero
      plugs := rfl
      linear := rfl }

def olhs4 : Term OM3 L4 OneSrt3.all :=
  Term.op (S := OM3) (Sum.inl OneOp3.out)
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

def octxt4 : Term OM3 (OneSrt3.all :: L4) OneSrt3.all :=
  Term.op (S := OM3) (Sum.inl OneOp3.out)
    (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil))

/-- The same rule with the sorts collapsed. -/
def Q4 : PositionedRewrite OM3 where
  ctx := L4
  sort := OneSrt3.all
  lhs := olhs4
  rhs := .var (.succ .zero)
  position :=
    { carrier := OneSrt3.all
      ctxt := octxt4
      redex := .var .zero
      plugs := rfl
      linear := rfl }

/-- Push a closing substitution across the collapse. -/
def pushClose (close : Sub sig3 K4 []) : Sub osig3 L4 [] := fun _ y =>
  match y with
  | .zero => collapse3.onTerm (close Srt3.nm Var.zero)
  | .succ .zero => collapse3.onTerm (close Srt3.pr (Var.succ Var.zero))
  | .succ (.succ v) => nomatch v

/-- The morphism, with a real instance map. -/
def Phi4 : RewriteMor P4 Q4 where
  sig := collapse3
  onSort := rfl
  onCarrier := rfl
  onInstance := fun I => { body := fun i => i.elim0, close := pushClose I.close }
  lhs_ok := fun _ => rfl
  rhs_ok := fun _ => rfl
  redex_ok := fun _ => rfl

/-- A closing substitution that exists. -/
def close0 : Sub sig3 K4 [] := fun _ y =>
  match y with
  | .zero => t3
  | .succ .zero => nilS
  | .succ (.succ v) => nomatch v

/-- ... and the instance it gives. -/
def I0 : RuleInstance [] P4 where
  body := fun i => i.elim0
  close := close0

/-- **The rule fires.** -/
theorem fires :
    RootStep P4 (Term.op (S := sig3) Op3.out (.cons t3 (.cons nilS .nil))) nilS :=
  ⟨I0, rfl, rfl⟩

/-- **And its firing arrives downstream.** -/
theorem image_fires :
    RootStep Q4 (Phi4.img (Term.op (S := sig3) Op3.out (.cons t3 (.cons nilS .nil))))
      (Phi4.img nilS) :=
  Phi4.rootStep_transport fires

/-- Possibility, non-vacuously. -/
theorem poss_here :
    Poss P4 (fun u => u = nilS)
      (Term.op (S := sig3) Op3.out (.cons t3 (.cons nilS .nil))) :=
  ⟨nilS, fires, rfl⟩

theorem poss_transported :
    Poss Q4 (Phi4.imgPred (fun u => u = nilS))
      (Phi4.img (Term.op (S := sig3) Op3.out (.cons t3 (.cons nilS .nil)))) :=
  Phi4.poss_transport poss_here

/-- The modality at the chosen position, non-vacuously: the chosen occurrence is
the channel, and placing the channel there steps to `nil`. -/
theorem steps_here : StepsFromPosition P4 (fun u => u = nilS) t3 :=
  ⟨I0, rfl, rfl⟩

theorem steps_transported :
    StepsFromPosition Q4 (Phi4.imgPred (fun u => u = nilS)) (Phi4.imgCarrier t3) :=
  Phi4.stepsFromPosition_transport steps_here

/-- The rule's only rely parameter is the continuation. -/
theorem p_is_rely : P4.RelyParameter (Var.succ Var.zero : Var K4 Srt3.pr) :=
  ⟨by decide, rfl⟩

def Aup4 : RelyTyping P4 := fun s => match s with
  | Srt3.nm => fun _ _ => True
  | Srt3.pr => fun _ v => v = nilS
  | Srt3.gh => fun _ _ => True

def Adown4 : RelyTyping Q4 := fun s => match s with
  | OneSrt3.all => fun _ v => v = nilO

/-- **The covering exists here.**  The upstream environment does not depend on
the downstream one, because the downstream assumptions pin the only value that
matters. -/
def covering4 : RewriteMor.EnvCovering Phi4 Aup4 Adown4 where
  lift := fun _ _ => relyEnvOf close0
  lift_ok := by
    intro _ _ _ x _
    cases x with
    | zero => exact True.intro
    | succ w =>
        cases w with
        | zero => rfl
        | succ v => exact nomatch v
  agree := by
    intro env' h I hag s y hy
    cases y with
    | zero => exact absurd hy.1 (by decide)
    | succ w =>
        cases w with
        | zero =>
            have hp : I.close Srt3.pr (Var.succ Var.zero) = nilS :=
              hag Srt3.pr (Var.succ Var.zero) p_is_rely
            have hq : env' OneSrt3.all (Var.succ Var.zero) hy = nilO := h _ _ hy
            show collapse3.onTerm (I.close Srt3.pr (Var.succ Var.zero)) = _
            rw [hp, hq]
            rfl
        | succ v => exact nomatch v

/-- The rely-indexed modality holds upstream. -/
theorem rely_here : RelyPossibly P4 Aup4 (fun u => u = nilS) t3 := by
  intro env henv
  refine ⟨I0, ?_, rfl, rfl⟩
  intro s x hx
  cases x with
  | zero => exact absurd hx.1 (by decide)
  | succ w =>
      cases w with
      | zero => exact (henv Srt3.pr (Var.succ Var.zero) p_is_rely).symm
      | succ v => exact nomatch v

/-- **... and travels, because the covering is available.** -/
theorem rely_transported :
    RelyPossibly Q4 Adown4 (Phi4.imgPred (fun u => u = nilS)) (Phi4.imgCarrier t3) :=
  Phi4.relyPossibly_transport covering4 rely_here

/-! ### Where transport really fails

The covering above existed because the downstream assumptions pinned the only
value that mattered.  Drop the assumptions and it does not, and the reason is
visible.  A change of signature carries values forward; the modality's universal
quantifier needs them carried back.  Collapsing sorts creates a closed
downstream term at the rely sort which is the image of no closed upstream term
of that sort, the downstream quantifier ranges over it, and the upstream
specification was never asked about it.

This is the same morphism as above -- every condition Section 19.8 places on one
holds, and the rule fires on both sides -- so what separates the two cases is
the rely typing alone. -/

/-- A downstream value that no upstream process maps to. -/
def aNameO : Term osig3 [] OneSrt3.all := Term.op (S := osig3) OneOp3.aName Args.nil

/-- A head test, since the term type is indexed and its constructors cannot be
compared directly. -/
def isAName : {Γ : Ctx osig3} → Term osig3 Γ OneSrt3.all → Bool
  | _, .var _ => false
  | _, .op OneOp3.aName _ => true
  | _, .op OneOp3.nil _ => false
  | _, .op OneOp3.out _ => false

theorem isAName_aNameO : isAName aNameO = true := rfl

/-- **The collapse is not surjective at the rely sort.**  Every closed process
maps to a term headed by `nil` or by `out`; none maps to the name. -/
theorem image_is_not_aName (w : Term sig3 [] Srt3.pr) :
    isAName (collapse3.onTerm w) = false := by
  cases w with
  | var v => cases v
  | op o args => cases o <;> rfl

theorem not_an_image (w : Term sig3 [] P4.sort) : Phi4.img w ≠ aNameO := by
  intro h
  have hw : isAName (collapse3.onTerm w) = false := image_is_not_aName w
  rw [show collapse3.onTerm w = Phi4.img w from rfl, h, isAName_aNameO] at hw
  exact absurd hw (by decide)

/-- No assumptions on either side: the rule relies on nothing in particular. -/
def freeUp : RelyTyping P4 := fun _ _ _ => True

def freeDown : RelyTyping Q4 := fun _ _ _ => True

/-- A target predicate that asks nothing, so nothing about it can be blamed. -/
def anyTarget : Term sig3 [] P4.sort → Prop := fun _ => True

/-- The downstream rely environment that escapes the image. -/
def escapingEnv : RelyEnv Q4 := fun _ _ _ => aNameO

/-- Downstream the continuation is still the rely parameter. -/
theorem q_is_rely : Q4.RelyParameter (Var.succ Var.zero : Var L4 OneSrt3.all) :=
  ⟨by decide, rfl⟩

/-- The closing substitution the rule supplies for a given rely environment:
the chosen channel at the position, and whatever the environment asked for at
the continuation. -/
def closeOf (env : RelyEnv P4) : Sub sig3 K4 []
  | _, .zero => t3
  | _, .succ .zero => env Srt3.pr (Var.succ Var.zero) p_is_rely
  | _, .succ (.succ v) => nomatch v

def instOf (env : RelyEnv P4) : RuleInstance [] P4 where
  body := fun i => i.elim0
  close := closeOf env

/-- **Upstream the specification holds, non-vacuously**: rely environments
exist, and the rule meets every one of them with an actual instance. -/
theorem free_rely_here : RelyPossibly P4 freeUp anyTarget t3 := by
  intro env _
  refine ⟨instOf env, ?_, rfl, trivial⟩
  intro _ x hx
  cases x with
  | zero => exact absurd hx.1 (by decide)
  | succ w =>
      cases w with
      | zero => rfl
      | succ v => exact nomatch v

/-- **Downstream it fails**, and for a reason no condition on the rule can
repair: the environment names a value outside the image of the translation. -/
theorem free_target_fails :
    ¬ RelyPossibly Q4 freeDown (Phi4.imgPred anyTarget) (Phi4.imgCarrier t3) := by
  intro h
  obtain ⟨J, hreal, -, hB⟩ := h escapingEnv (fun _ _ _ => trivial)
  obtain ⟨w, -, hw⟩ := hB
  have hj : J.close OneSrt3.all (Var.succ Var.zero) = aNameO := hreal _ _ q_is_rely
  exact not_an_image w (hw.symm.trans hj)

/-- **The rely-indexed modality does not transport along a morphism of
theories** -- the corrected witness.  Both sides fire, both sides have
environments, and the specification separates them. -/
theorem relyPossibly_does_not_transport :
    RelyPossibly P4 freeUp anyTarget t3
      ∧ ¬ RelyPossibly Q4 freeDown (Phi4.imgPred anyTarget) (Phi4.imgCarrier t3) :=
  ⟨free_rely_here, free_target_fails⟩

/-- **And the covering is exactly what is missing.** -/
theorem no_env_covering : ¬ Nonempty (RewriteMor.EnvCovering Phi4 freeUp freeDown) := by
  rintro ⟨C⟩
  exact free_target_fails (Phi4.relyPossibly_transport C free_rely_here)

/-- One morphism, two rely typings, transport at one and not at the other.  So
the covering is a datum a change of theory must supply, not a property it can be
asked to have. -/
theorem covering_is_a_datum_not_a_property :
    Nonempty (RewriteMor.EnvCovering Phi4 Aup4 Adown4)
      ∧ ¬ Nonempty (RewriteMor.EnvCovering Phi4 freeUp freeDown) :=
  ⟨⟨covering4⟩, no_env_covering⟩

end Collapsing

end Mettapedia.OSLF.Binding
