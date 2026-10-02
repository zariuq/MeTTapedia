import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Soundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchLawsControls

/-!
# Controls for the soundness of the annotated calculus

The rule packages here have a universe at each level and a ground type as heads
(`CtlHead`); the readings send every universe to the universe and the ground head to a
ground type (`ctlReading`), and satisfy the conditions on heads of a valid reading
(`ctlValid`).

**Positive: closed instances of soundness.**

* Typing, in the package without declarations: the identity on `U₀` denotes the function
  carrying the domain `U` that returns its argument, an element of `U → U`
  (`idU_sound`).
* Equality: the identity on `Σ U₀ U₀` and its η-expansion `λ p. (p.1, p.2)` are equal by
  a derivation (`eta_pair_derivable`), so they denote alike (`eta_pair_sound`); the
  interpretation of terms whose functions carry no domain separates them.
* A root step validated through spine facts: with the constant `idc : U₀ → U₀` read as
  the identity carrying its declared type, the root step `idc a ⟶ a` is valid at every
  instance (`idcReading_valid`), and the derivable equation `idc G ≡ G`, at the ground
  head `G`, holds of the denotations (`idc_root_sound`).
* Refl facts: for the constant `rc : Π (A : U₁) (x : A). Id A x x → U₀`, the derivable
  typing of `rc U₀ G (refl G)` gives, by soundness, that the path's parameter type is an
  identity type between the denotation of `G` and itself (`rc_reflFact`).

**Negative: invalid readings break a soundness case.**

* A constant whose value is not an element of its declared type: reading `c : U₀` as
  zero, the derivable typing `c : U₀` is not sound (`zeroReading_unsound`), the reading
  fails the condition on constants (`zeroReading_constants_fail`), and it is not valid
  (`zeroReading_not_valid`).
* A root step that the reading does not validate: reading `c, d : U₀` as the universe
  and the numbers, with the root step `c ⟶ d`, the condition on constants holds
  (`cdReading_constants`), and the derivable equation `c ≡ d` is not sound
  (`cdReading_unsound`), so the reading is not valid (`cdReading_not_valid`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated
namespace SoundnessControls

open Impredicative.Domain
open Impredicative.Domain.Ideal (projT TypeGenerated principal univIdeal natI zeroI Cont cpi csigma
  clam instPi)

/-! ## The heads of the control packages -/

/-- The heads of the control packages: a universe at each level, and a ground type. -/
inductive CtlHead where
  | univ (level : Nat)
  | ground
  deriving DecidableEq

/-- A universe is typed by the universe one level up, and the ground type by the
universe at level zero. -/
inductive CtlHead.Typing : CtlHead → CtlHead → Prop where
  | univ (level : Nat) : Typing (.univ level) (.univ (level + 1))
  | ground : Typing .ground (.univ 0)

inductive CtlHead.IsUniverse : CtlHead → Prop where
  | univ (level : Nat) : IsUniverse (.univ level)

/-- Two universes join at the larger level. -/
inductive CtlHead.Join : CtlHead → CtlHead → CtlHead → Prop where
  | univ (left right : Nat) : Join (.univ left) (.univ right) (.univ (max left right))

/-- Universes are cumulative along their levels. -/
def CtlHead.Cumulative : CtlHead → CtlHead → Prop
  | .univ left, .univ right => left ≤ right
  | _, _ => False

/-- A rule package over the control heads, with declarations. -/
def ctlRules (constantType : DeclName → Option (Tm CtlHead 0))
    (computation : RootComputation CtlHead) : Rules CtlHead where
  headTyping := CtlHead.Typing
  isUniverse := CtlHead.IsUniverse
  join := CtlHead.Join
  cumulative := CtlHead.Cumulative
  headEq := Eq
  constantType := constantType
  computation := computation

/-- The element of a control head: every universe is the universe, and the ground
type a ground type. -/
def ctlHead : CtlHead → List Tok
  | .univ _ => Elem.univ
  | .ground => Elem.ground

/-- The reading of the control heads, with the constants read by `const`. -/
def ctlReading (const : DeclName → Ideal) : Reading CtlHead := ⟨ctlHead, const⟩

/-- **The conditions on heads** hold for the reading of the control heads: a reading of
a control package is valid when its constants and root steps are. -/
theorem ctlValid {ct : DeclName → Option (Tm CtlHead 0)} {comp : RootComputation CtlHead}
    {P : ChurchRules (ctlRules ct comp)} {const : DeclName → Ideal}
    (constants : ∀ {c : DeclName} {D : CTm CtlHead 0}, P.constantType c = some D →
      TypeGenerated (cinterp (ctlReading const) D Env.nil) →
        projT (cinterp (ctlReading const) D Env.nil) (const c) = const c)
    (roots : ∀ {n : Nat} {l r : CTm CtlHead n} {τ : Ideal} {ρ : Env n},
      P.computation.step l r → TypeGenerated τ →
      projT τ (cinterp (ctlReading const) l ρ) = cinterp (ctlReading const) l ρ →
      SpineFacts (ctlReading const) P l τ ρ →
      projT τ (cinterp (ctlReading const) r ρ) = cinterp (ctlReading const) r ρ →
      SpineFacts (ctlReading const) P r τ ρ →
      cinterp (ctlReading const) l ρ = cinterp (ctlReading const) r ρ) :
    ReadingValid (ctlReading const) P where
  universes := by
    intro h hu
    cases hu
    rfl
  headTyping := by
    intro h u typing
    cases typing with
    | univ l => exact ⟨rfl, Elem.ty_univ_univ⟩
    | ground => exact ⟨rfl, Elem.ty_tag (k := .ground) trivial Elem.isUniv_univ⟩
  join := by
    intro u v w _ _ join
    cases join
    rfl
  cumulative := by
    intro u v c
    cases u with
    | univ l =>
        cases v with
        | univ r => rfl
        | ground => exact c.elim
    | ground => exact c.elim
  headEq := by
    intro h h' e
    change h = h' at e
    rw [e]
  constants := constants
  roots := roots

/-- The universe at level zero. -/
abbrev U₀ {n : Nat} : CTm CtlHead n := .head (.univ 0)

/-- The universe at level one. -/
abbrev U₁ {n : Nat} : CTm CtlHead n := .head (.univ 1)

/-- The ground head. -/
abbrev G {n : Nat} : CTm CtlHead n := .head .ground

/-- The denotation of the ground head. -/
def groundIdeal : Ideal := principal Elem.ground

/-! ## Positive: the package without declarations -/

/-- The control package without declarations. -/
def R₀ : Rules CtlHead := ctlRules (fun _ => none) .empty

/-- The control package without declarations, annotated. -/
def P₀ : ChurchRules R₀ := ChurchRules.empty R₀ (fun _ => rfl)

/-- The reading of the control package without declarations. -/
def reading₀ : Reading CtlHead := ctlReading fun _ => Ideal.bot

theorem reading₀_valid : ReadingValid reading₀ P₀ :=
  ctlValid (fun h _ => by cases h) (fun step => step.elim)

section Ctl₀

variable {n : Nat} {Γ : CCtx CtlHead n}

theorem U₀_typed₀ : CTyped P₀ Γ U₀ U₁ := .headType (CtlHead.Typing.univ 0)

/-- The identity on `U₀`. -/
theorem idU_typed : CTyped P₀ .nil (.lam U₀ (.var 0)) (.pi U₀ U₀) :=
  .lamIntro U₀_typed₀ (CtlHead.IsUniverse.univ _)
    (.piForm U₀_typed₀ (CtlHead.IsUniverse.univ _) U₀_typed₀ (CtlHead.IsUniverse.univ _)
      (CtlHead.Join.univ _ _)) (CtlHead.IsUniverse.univ _) (.var 0)

end Ctl₀

/-- **Positive, typing**: the identity on `U₀` denotes the function carrying the domain
`U` that returns its argument, an element of `U → U`. -/
theorem idU_sound :
    projT (cpi univIdeal fun _ => univIdeal) (clam univIdeal fun y => y) =
      clam univIdeal fun y => y :=
  (CTyped.sound reading₀_valid idU_typed (ρ := Env.nil) trivial).2.1

/-- `Σ U₀ U₀`. -/
abbrev S {n : Nat} : CTm CtlHead n := .sigma U₀ U₀

theorem S_typed {n : Nat} {Γ : CCtx CtlHead n} :
    CTyped P₀ Γ S (.head (.univ (max 1 1))) :=
  .sigmaForm U₀_typed₀ (CtlHead.IsUniverse.univ _) U₀_typed₀ (CtlHead.IsUniverse.univ _)
    (CtlHead.Join.univ _ _)

/-- **The η pair is derivably equal**: `λ (p : Σ U₀ U₀). p ≡ λ (p : Σ U₀ U₀). (p.1, p.2)`. -/
theorem eta_pair_derivable :
    CEqual P₀ .nil (.lam S (.var 0)) (.lam S (.pair (.fst (.var 0)) (.snd (.var 0))))
      (.pi S S) := by
  have tv : CTyped P₀ (.snoc .nil S) (.var 0) S := .var 0
  have tfst : CTyped P₀ (.snoc .nil S) (.fst (.var 0)) U₀ := .fstElim tv
  have tsnd : CTyped P₀ (.snoc .nil S) (.snd (.var 0)) (CTm.inst0 (.fst (.var 0)) U₀) :=
    .sndElim tv
  have tpair : CTyped P₀ (.snoc .nil S) (.pair (.fst (.var 0)) (.snd (.var 0))) S :=
    .pairIntro S_typed (CtlHead.IsUniverse.univ _) tfst tsnd
  have e₁ : CEqual P₀ (.snoc .nil S) (.fst (.var 0))
      (.fst (.pair (.fst (.var 0)) (.snd (.var 0)))) U₀ :=
    .symm (.betaFst S_typed (CtlHead.IsUniverse.univ _) tfst tsnd)
  have e₂ : CEqual P₀ (.snoc .nil S) (.snd (.var 0))
      (.snd (.pair (.fst (.var 0)) (.snd (.var 0)))) (CTm.inst0 (.fst (.var 0)) U₀) :=
    .symm (.betaSnd S_typed (CtlHead.IsUniverse.univ _) tfst tsnd)
  exact .lamCong (.refl S_typed) (CtlHead.IsUniverse.univ _)
    (.piForm S_typed (CtlHead.IsUniverse.univ _) S_typed (CtlHead.IsUniverse.univ _)
      (CtlHead.Join.univ _ _)) (CtlHead.IsUniverse.univ _) (.etaSigma tv tpair e₁ e₂)

/-- **Positive, equality**: the identity on `Σ U₀ U₀` and its η-expansion denote
alike. -/
theorem eta_pair_sound :
    clam (csigma univIdeal fun _ => univIdeal) (fun y => y) =
      clam (csigma univIdeal fun _ => univIdeal)
        (fun y => Ideal.pair (Ideal.fst y) (Ideal.snd y)) :=
  CEqual.sound reading₀_valid eta_pair_derivable (ρ := Env.nil) trivial

/-! ## Positive: a root step validated through spine facts -/

/-- The identity constant on `U₀`. -/
def idcName : DeclName := .num .anonymous 0

/-- Its declared type `U₀ → U₀`, unannotated. -/
def idcType : Tm CtlHead 0 := .pi (.head (.univ 0)) (.head (.univ 0))

/-- Its declared type `U₀ → U₀`, annotated. -/
def idcTypeC : CTm CtlHead 0 := .pi U₀ U₀

/-- The root computation `idc a ⟶ a`, unannotated. -/
def idcComputation : RootComputation CtlHead where
  step := fun l r => l = .app (.const idcName) r
  rename := by
    intro n m ρ l r h
    subst h
    rfl
  substitute := by
    intro n m σ l r h
    subst h
    rfl

/-- The root computation `idc a ⟶ a`, annotated. -/
def idcCComputation : CRootComputation CtlHead where
  step := fun l r => l = .app (.const idcName) r
  rename := by
    intro n m ρ l r h
    subst h
    rfl
  substitute := by
    intro n m σ l r h
    subst h
    rfl

/-- The package declaring `idc : U₀ → U₀` with `idc a ⟶ a`. -/
def Rid : Rules CtlHead :=
  ctlRules (fun c => if c = idcName then some idcType else none) idcComputation

/-- The package declaring `idc : U₀ → U₀` with `idc a ⟶ a`, annotated. -/
def Pid : ChurchRules Rid where
  constantType := fun c => if c = idcName then some idcTypeC else none
  computation := idcCComputation
  erase_constantType := fun name =>
    apply_ite (Option.map CTm.erase) (name = idcName) (some idcTypeC) none
  erase_step := by
    intro n l r h
    subst h
    rfl

/-- The value of `idc`: the identity projected onto its declared type. -/
def idcValue : Ideal := projT (cpi univIdeal fun _ => univIdeal) (Ideal.lam fun X => principal X)

/-- The reading of `idc` as the identity carrying its declared type. -/
def idcReading : Reading CtlHead := ctlReading fun _ => idcValue

theorem idc_declared : Pid.constantType idcName = some idcTypeC :=
  show (if idcName = idcName then some idcTypeC else none) = some idcTypeC from if_pos rfl

/-- **The reading of `idc` is valid**: its value is an element of its declared type,
and the spine facts of the left side of `idc a ⟶ a` make the argument an element of
`U₀`, which the value returns. -/
theorem idcReading_valid : ReadingValid idcReading Pid := by
  refine ctlValid (fun {c D} h _ => ?_) (fun {n l r τ ρ} step _ _ sl hr _ => ?_)
  · have hD : D = idcTypeC := by
      change (if c = idcName then some idcTypeC else none) = some D at h
      split at h
      · exact (Option.some.inj h).symm
      · cases h
    subst hD
    exact Ideal.projT_projT _ _
  · change l = .app (.const idcName) r at step
    subst step
    obtain ⟨⟨hτ, spine⟩, -⟩ := SpineFacts.constSpine (args := [r]) idc_declared sl
    refine Ideal.churchConst_root (churchTele_cinterp _ idcTypeC Env.nil) (Nat.le_refl _)
      spine (Ideal.app_lam_principal Ideal.Cont.id _) ?_
    rw [hτ]
    exact hr

section Idc

variable {n : Nat} {Γ : CCtx CtlHead n}

theorem U₀_typed_id : CTyped Pid Γ U₀ U₁ := .headType (CtlHead.Typing.univ 0)

theorem G_typed_id : CTyped Pid Γ G U₀ := .headType CtlHead.Typing.ground

theorem idc_typed : CTyped Pid Γ (.const idcName) (.pi U₀ U₀) :=
  .const idc_declared
    (.piForm U₀_typed_id (CtlHead.IsUniverse.univ _) U₀_typed_id (CtlHead.IsUniverse.univ _)
      (CtlHead.Join.univ _ _)) (CtlHead.IsUniverse.univ _)

/-- `idc G ≡ G : U₀`, by the root step. -/
theorem idc_root_derivable : CEqual Pid .nil (.app (.const idcName) G) G U₀ :=
  .rootFree rfl (.appElim idc_typed G_typed_id) G_typed_id

end Idc

/-- **Positive, root step**: `idc G` denotes the ground type. -/
theorem idc_root_sound : Ideal.app idcValue groundIdeal = groundIdeal :=
  CEqual.sound idcReading_valid idc_root_derivable (ρ := Env.nil) trivial

/-! ## Positive: refl facts from soundness -/

/-- A constant taking a reflexivity. -/
def rcName : DeclName := .num .anonymous 1

/-- Its declared type `Π (A : U₁) (x : A). Id A x x → U₀`, unannotated. -/
def rcType : Tm CtlHead 0 :=
  .pi (.head (.univ 1)) (.pi (.var 0)
    (.pi (.id (.var 1) (.var 0) (.var 0)) (.head (.univ 0))))

/-- Its declared type `Π (A : U₁) (x : A). Id A x x → U₀`, annotated. -/
def rcTypeC : CTm CtlHead 0 := .pi U₁ (.pi (.var 0) (.pi (.id (.var 1) (.var 0) (.var 0)) U₀))

/-- The package declaring `rc`. -/
def Rrc : Rules CtlHead := ctlRules (fun c => if c = rcName then some rcType else none) .empty

/-- The package declaring `rc`, annotated. -/
def Prc : ChurchRules Rrc where
  constantType := fun c => if c = rcName then some rcTypeC else none
  computation := .empty
  erase_constantType := fun name =>
    apply_ite (Option.map CTm.erase) (name = rcName) (some rcTypeC) none
  erase_step := fun h => h.elim

/-- The reading of `rc` as the least element. -/
def rcReading : Reading CtlHead := ctlReading fun _ => Ideal.bot

theorem rcReading_valid : ReadingValid rcReading Prc :=
  ctlValid (fun _ _ => Ideal.le_antisymm (Ideal.projT_le _ _) (Ideal.bot_le _))
    (fun step => step.elim)

theorem rc_declared : Prc.constantType rcName = some rcTypeC :=
  show (if rcName = rcName then some rcTypeC else none) = some rcTypeC from if_pos rfl

section Rc

theorem U₁_typed_rc {n : Nat} {Γ : CCtx CtlHead n} :
    CTyped Prc Γ U₁ (.head (.univ 2)) :=
  .headType (CtlHead.Typing.univ _)

theorem U₀_typed_rc {n : Nat} {Γ : CCtx CtlHead n} : CTyped Prc Γ U₀ U₁ :=
  .headType (CtlHead.Typing.univ 0)

theorem G_typed_rc {n : Nat} {Γ : CCtx CtlHead n} : CTyped Prc Γ G U₀ :=
  .headType CtlHead.Typing.ground

/-- The declared type of `rc` is formed. -/
theorem rcType_typed :
    CTyped Prc .nil rcTypeC
      (.head (.univ (max 2 (max 1 (max 1 1))))) := by
  have tA : CTyped Prc (.snoc .nil U₁) (.var 0) U₁ := .var 0
  have tx : CTyped Prc (.snoc (.snoc .nil U₁) (.var 0)) (.var 0) (.var 1) := .var 0
  have tA' : CTyped Prc (.snoc (.snoc .nil U₁) (.var 0)) (.var 1) U₁ := .var 1
  have tId : CTyped Prc (.snoc (.snoc .nil U₁) (.var 0)) (.id (.var 1) (.var 0) (.var 0)) U₁ :=
    .idForm tA' (CtlHead.IsUniverse.univ _) tx tx
  have tIdPi : CTyped Prc (.snoc (.snoc .nil U₁) (.var 0))
      (.pi (.id (.var 1) (.var 0) (.var 0)) U₀)
      (.head (.univ (max 1 1))) :=
    .piForm tId (CtlHead.IsUniverse.univ _) U₀_typed_rc (CtlHead.IsUniverse.univ _)
      (CtlHead.Join.univ _ _)
  have tInner : CTyped Prc (.snoc .nil U₁) (.pi (.var 0) (.pi (.id (.var 1) (.var 0) (.var 0)) U₀))
      (.head (.univ (max 1 (max 1 1)))) :=
    .piForm tA (CtlHead.IsUniverse.univ _) tIdPi (CtlHead.IsUniverse.univ _) (CtlHead.Join.univ _ _)
  exact .piForm U₁_typed_rc (CtlHead.IsUniverse.univ _) tInner (CtlHead.IsUniverse.univ _)
    (CtlHead.Join.univ _ _)

/-- `rc U₀ G (refl G) : U₀`. -/
theorem rc_spine_typed :
    CTyped Prc .nil (CTm.appSpine (.const rcName) ([U₀, G] ++ [.refl G])) U₀ := by
  have trc : CTyped Prc .nil (.const rcName) rcTypeC :=
    .const rc_declared rcType_typed (CtlHead.IsUniverse.univ _)
  have t₁ : CTyped Prc .nil (.app (.const rcName) U₀)
      (.pi U₀ (.pi (.id U₀ (.var 0) (.var 0)) U₀)) := .appElim trc U₀_typed_rc
  have t₂ : CTyped Prc .nil (.app (.app (.const rcName) U₀) G) (.pi (.id U₀ G G) U₀) :=
    .appElim t₁ G_typed_rc
  exact .appElim t₂ (.reflIntro G_typed_rc)

end Rc

/-- **Positive, refl facts**: soundness of the typing of `rc U₀ G (refl G)` gives that
the path's parameter type is an identity type between the denotation of `G` and
itself, of whose carrier it is an element. -/
theorem rc_reflFact :
    ∃ T : Ideal,
      Ideal.dom .pi (instPi (cinterp rcReading rcTypeC Env.nil) [univIdeal, groundIdeal]) =
        Ideal.ident T groundIdeal groundIdeal ∧ projT T groundIdeal = groundIdeal :=
  SpineFacts.reflArg rc_declared (as := [U₀, G]) (bs := [])
    (CTyped.sound rcReading_valid rc_spine_typed (ρ := Env.nil) trivial).2.2

/-! ## Negative: a constant whose value is not an element of its declared type -/

/-- The constant `c`. -/
def cName : DeclName := .num .anonymous 2

/-- The constant `d`. -/
def dName : DeclName := .num .anonymous 3

theorem dName_ne_cName : dName ≠ cName := by
  intro h
  injection h with _ h'
  exact absurd h' (by decide)

/-- The package declaring `c : U₀`. -/
def Rc : Rules CtlHead :=
  ctlRules (fun n => if n = cName then some (.head (.univ 0)) else none) .empty

/-- The package declaring `c : U₀`, annotated. -/
def Pc : ChurchRules Rc where
  constantType := fun n => if n = cName then some U₀ else none
  computation := .empty
  erase_constantType := fun name =>
    apply_ite (Option.map CTm.erase) (name = cName) (some U₀) none
  erase_step := fun h => h.elim

theorem c_declared : Pc.constantType cName = some U₀ :=
  show (if cName = cName then some U₀ else none) = some U₀ from if_pos rfl

theorem c_typed : CTyped Pc .nil (.const cName) U₀ :=
  .const c_declared (.headType (CtlHead.Typing.univ 0)) (CtlHead.IsUniverse.univ _)

/-- The reading of `c` as zero. -/
def zeroReading : Reading CtlHead := ctlReading fun _ => zeroI

/-- **Negative**: reading `c : U₀` as zero breaks the soundness of the derivable typing
`c : U₀`: zero is not an element of the universe. -/
theorem zeroReading_unsound :
    ¬ (CStatement.typing .nil (.const cName) (U₀ : CTm CtlHead 0)).Sound zeroReading Pc := by
  intro h
  obtain ⟨-, hz, -⟩ := h Env.nil trivial
  exact ChurchLawsControls.zero_not_typeGenerated (Ideal.projT_univ_eq_self_iff.1 hz)

/-- The condition on constants fails for the reading of `c` as zero. -/
theorem zeroReading_constants_fail :
    ¬ ∀ {c : DeclName} {D : CTm CtlHead 0}, Pc.constantType c = some D →
      TypeGenerated (cinterp zeroReading D Env.nil) →
        projT (cinterp zeroReading D Env.nil) (zeroReading.const c) = zeroReading.const c := by
  intro h
  have hz := h (c := cName) (D := U₀) c_declared
    (Ideal.typeGenerated_principal Elem.ty_univ_univ)
  exact ChurchLawsControls.zero_not_typeGenerated (Ideal.projT_univ_eq_self_iff.1 hz)

/-- **Negative**: the reading of `c` as zero is not valid. -/
theorem zeroReading_not_valid : ¬ ReadingValid zeroReading Pc :=
  fun valid => zeroReading_unsound (CDerivable.sound valid c_typed)

/-! ## Negative: a root step that the reading does not validate -/

/-- The root computation `c ⟶ d`, unannotated. -/
def cdComputation : RootComputation CtlHead where
  step := fun l r => l = .const cName ∧ r = .const dName
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The root computation `c ⟶ d`, annotated. -/
def cdCComputation : CRootComputation CtlHead where
  step := fun l r => l = .const cName ∧ r = .const dName
  rename := by
    rintro n m ρ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The package declaring `c d : U₀` with `c ⟶ d`. -/
def Rcd : Rules CtlHead :=
  ctlRules (fun n => if n = cName ∨ n = dName then some (.head (.univ 0)) else none)
    cdComputation

/-- The package declaring `c d : U₀` with `c ⟶ d`, annotated. -/
def Pcd : ChurchRules Rcd where
  constantType := fun n => if n = cName ∨ n = dName then some U₀ else none
  computation := cdCComputation
  erase_constantType := fun name =>
    apply_ite (Option.map CTm.erase) (name = cName ∨ name = dName) (some U₀) none
  erase_step := by
    rintro n l r ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The reading of `c` as the universe and of every other constant as the numbers. -/
def cdReading : Reading CtlHead := ctlReading fun n => if n = cName then univIdeal else natI

theorem cdReading_c : cdReading.const cName = univIdeal :=
  show (if cName = cName then univIdeal else natI) = univIdeal from if_pos rfl

theorem cdReading_d : cdReading.const dName = natI :=
  show (if dName = cName then univIdeal else natI) = natI from if_neg dName_ne_cName

/-- **The condition on constants holds** for the reading of `c` and `d` as the universe
and the numbers: both are types. -/
theorem cdReading_constants :
    ∀ {c : DeclName} {D : CTm CtlHead 0}, Pcd.constantType c = some D →
      TypeGenerated (cinterp cdReading D Env.nil) →
        projT (cinterp cdReading D Env.nil) (cdReading.const c) = cdReading.const c := by
  intro c D h _
  have hD : D = U₀ := by
    change (if c = cName ∨ c = dName then some U₀ else none) = some D at h
    split at h
    · exact (Option.some.inj h).symm
    · cases h
  subst hD
  change projT univIdeal (if c = cName then univIdeal else natI) =
    (if c = cName then univIdeal else natI)
  split
  · exact Impredicative.Domain.EliminatorControls.univ_type
  · exact Impredicative.Domain.EliminatorControls.natI_type

theorem c_declared_cd : Pcd.constantType cName = some U₀ :=
  show (if cName = cName ∨ cName = dName then some U₀ else none) = some U₀ from if_pos (Or.inl rfl)

theorem d_declared_cd : Pcd.constantType dName = some U₀ :=
  show (if dName = cName ∨ dName = dName then some U₀ else none) = some U₀ from if_pos (Or.inr rfl)

theorem c_typed_cd : CTyped Pcd .nil (.const cName) U₀ :=
  .const c_declared_cd (.headType (CtlHead.Typing.univ 0)) (CtlHead.IsUniverse.univ _)

theorem d_typed_cd : CTyped Pcd .nil (.const dName) U₀ :=
  .const d_declared_cd (.headType (CtlHead.Typing.univ 0)) (CtlHead.IsUniverse.univ _)

/-- `c ≡ d : U₀`, by the root step. -/
theorem cd_derivable : CEqual Pcd .nil (.const cName) (.const dName) U₀ :=
  .rootFree ⟨rfl, rfl⟩ c_typed_cd d_typed_cd

/-- **Negative**: the derivable equation `c ≡ d` is not sound for the reading of `c` and
`d` as the universe and the numbers. -/
theorem cdReading_unsound :
    ¬ (CStatement.equality .nil (.const cName) (.const dName) (U₀ : CTm CtlHead 0)).Sound
      cdReading Pcd := by
  intro h
  have e : cdReading.const cName = cdReading.const dName := (h Env.nil trivial).1
  rw [cdReading_c, cdReading_d] at e
  have hu : natI.Mem (.tag .univ) := e ▸ ChurchLawsControls.univ_mem_univ
  change ent Elem.nat (.tag .univ) = true at hu
  simp [ent_tag, hasTag, Elem.nat] at hu

/-- **Negative**: the reading of `c` and `d` as the universe and the numbers is not
valid, though its constants are elements of their declared types: its root step is
not. -/
theorem cdReading_not_valid : ¬ ReadingValid cdReading Pcd :=
  fun valid => cdReading_unsound (CDerivable.sound valid cd_derivable)

end SoundnessControls
end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
