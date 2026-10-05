import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchModel

/-!
# Packages that contain the object package

The adequacy of the object package's constants is proved once, for every package that
contains the object package and reads its constants as the object reading does
(`ObjectExtension`). The object package is the instance with nothing added; the object package
with a declared datatype is another.

**An extension** carries:

* a package `church` containing the object package (`sub`), with the object package's root
  steps and their premises (`within`), a level model, and the object package's head typings
  and ground head equality;
* a valid reading that agrees with the object reading on the heads and on every constant the
  object package declares;
* roles that agree with the object package's on its constants, with root shape and
  deterministic annotated root steps;
* its declared datatypes, their parameters and constructors, the numbers among them, each
  datatype an inductive type and each constructor a constructor of its arity under the roles,
  and the inductive types read with their datatype's tag.

**What it gives** (`ObjectExtension.rigid`, `ObjectExtension.head`): the object package's rigid
types with the declared datatypes, and the weak-head reduction of the package's annotated terms
under its roles (`headReductionOf`, built from the roles alone, so the object package's own
reduction is an instance). With them: the conditions of the fundamental lemma (`groundHeads`,
`decoderStuck`, `neutralNormal`), the fundamental lemma within adequate constants of the object
package (`ObjectExtension.valid_within`), derivations of the object package lifted
(`ObjectExtension.lift`), the reading of the object package's terms (`cinterp_eq`), and the
scrutinee congruences of the object package's computing constants.

Positive example: the object package is an extension of itself (`objectExtension`, where the
object package's weak-head reduction is defined). Negative example: a package whose roles make
the decoder rigid is not one, since the roles must agree with the object package's on the
decoder (`ObjectExtension.roles_holds`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Package (jName numRecName iterName)
open Mettapedia.Logic

namespace CodeModel

/-! ## The weak-head reduction of a package with roles -/

/-- **The weak-head reduction of a package's annotated terms under roles** with root shape and
deterministic annotated root steps: the decoder computes on its code, the type of proposition
codes is rigid, each declared datatype is an inductive type, each constructor a constructor of
its arity, and the ground types are weak-head normal. -/
def headReductionOf {R : Rules Tower.Head} {P : ChurchRules R} (K : RigidTypes P)
    (roles : Roles Tower.Head) (shape : RootShape R roles)
    (deterministic : ∀ {n : Nat} {t u u' : CTm Tower.Head n}, P.computation.step t u →
      P.computation.step t u' → u = u')
    (holds : roles K.holds = .computes 1 (.split 0 .constructor fun _ => .leaf))
    (prop : roles K.prop = .rigid)
    (data : ∀ {d : DeclName}, K.data d → ∃ cs, roles d = .inductive cs)
    (ctor : ∀ {d c : DeclName} {fs : List FieldShape}, K.ctor d c fs →
      roles c = .constructor fs.length)
    (ground : ∀ {n : Nat} {g : CTm Tower.Head n}, K.ground g → Whnf R roles g.erase) :
    HeadReduction P K where
  step := CWhStepR P roles
  beta := .beta
  appFun := fun _ s => .appFun s
  root := .root
  holdsArg := fun s => CWhStepR.scrutinee (before := []) (after := []) holds rfl s
  deterministic := fun s s' => (CWhStepR.deterministic shape deterministic s s').symm
  head_normal := fun h u => CWhStepR.not_of_whnf (head_whnf shape h) u
  pi_normal := fun A B u => CWhStepR.not_of_whnf (pi_whnf shape A.erase B.erase) u
  id_normal := fun A a b u => CWhStepR.not_of_whnf (id_whnf shape A.erase a.erase b.erase) u
  refl_normal := fun a u => CWhStepR.not_of_whnf (refl_whnf shape a.erase) u
  prop_normal := fun u => CWhStepR.not_of_whnf
    (constSpine_whnf shape (args := []) fun _ _ h => nomatch prop.symm.trans h) u
  data_normal := fun u hd => by
    obtain ⟨cs, role⟩ := data hd
    exact CWhStepR.not_of_whnf (inductive_whnf shape role) u
  ctor_normal := fun {_ _ c fs ms} u hc _ => CWhStepR.not_of_whnf
    (canonical_whnf shape (.inr ⟨c, fs.length, _, ctor hc, CTm.erase_appSpine _ ms⟩)) u
  fstPair := .fstPair
  sndPair := .sndPair
  fst := .fst
  snd := .snd
  sigma_normal := fun A B u => CWhStepR.not_of_whnf (sigma_whnf shape A.erase B.erase) u
  ground_normal := fun u hg => CWhStepR.not_of_whnf (ground hg) u

theorem headReductionOf_step {R : Rules Tower.Head} {P : ChurchRules R} {K : RigidTypes P}
    {roles : Roles Tower.Head} {shape : RootShape R roles}
    {deterministic : ∀ {n : Nat} {t u u' : CTm Tower.Head n}, P.computation.step t u →
      P.computation.step t u' → u = u'}
    {holds : roles K.holds = .computes 1 (.split 0 .constructor fun _ => .leaf)}
    {prop : roles K.prop = .rigid}
    {data : ∀ {d : DeclName}, K.data d → ∃ cs, roles d = .inductive cs}
    {ctor : ∀ {d c : DeclName} {fs : List FieldShape}, K.ctor d c fs →
      roles c = .constructor fs.length}
    {ground : ∀ {n : Nat} {g : CTm Tower.Head n}, K.ground g → Whnf R roles g.erase}
    {n : Nat} {t u : CTm Tower.Head n} :
    (headReductionOf K roles shape deterministic holds prop data ctor ground).step t u ↔
      CWhStepR P roles t u :=
  Iff.rfl

/-! ## Rigid constants of the object package -/

theorem objectRoles_propRigid : objectRoles propN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans
    (roles_of_not_mem (by decide))

theorem objectRoles_setRigid : objectRoles setN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_set

/-! ## Extensions -/

/-- **A package containing the object package**, read in the domain as the object package is,
with roles, declared datatypes and their constructors for its weak-head reduction. -/
structure ObjectExtension where
  /-- The rule package. -/
  rules : Rules Tower.Head
  /-- Its annotation. -/
  church : ChurchRules rules
  /-- It contains the object package. -/
  sub : ChurchRulesSub objectChurch church
  /-- It has the object package's root steps, with their premises. -/
  within : StepsWithin objectChurch church
  /-- Its level model. -/
  levels : LevelModel rules ℕ
  /-- Its head typings are the object package's. -/
  headTyping : ∀ {h u : Tower.Head}, rules.headTyping h u → objectRules.headTyping h u
  /-- Head equality is trivial on the heads that are not universes. -/
  groundHeadEq : GroundHeadEq rules
  /-- Its reading in the domain. -/
  reading : Reading Tower.Head
  /-- The reading validates the package. -/
  valid : ReadingValid reading church
  /-- The reading reads the heads as the object reading. -/
  reading_head : reading.head = objectChurchReading.head
  /-- The reading reads the object package's constants as the object reading. -/
  reading_const : ∀ {c : DeclName}, (objectRules.constantType c).isSome = true →
    reading.const c = objectChurchReading.const c
  /-- The roles of its constants. -/
  roles : Roles Tower.Head
  /-- The roles of the object package's constants are the object package's. -/
  roles_object : ∀ {c : DeclName}, (objectRules.constantType c).isSome = true →
    roles c = objectRoles c
  /-- The package has root shape under its roles. -/
  shape : RootShape rules roles
  /-- Its annotated root steps are deterministic. -/
  deterministic : ∀ {n : Nat} {t u u' : CTm Tower.Head n}, church.computation.step t u →
    church.computation.step t u' → u = u'
  /-- Its declared datatypes. -/
  data : DeclName → Prop
  /-- Their parameters. -/
  params : DeclName → List (CTm Tower.Head 0)
  /-- Their constructors, with the shapes of their fields. -/
  ctor : DeclName → DeclName → List FieldShape → Prop
  ctor_data : ∀ {d c : DeclName} {fs : List FieldShape}, ctor d c fs → data d
  zero_ctor : ctor numN zeroN []
  suc_ctor : ctor numN sucN [.self]
  /-- Each declared datatype is an inductive type under the roles. -/
  data_role : ∀ {d : DeclName}, data d → ∃ cs, roles d = .inductive cs
  /-- Each constructor is a constructor of its arity under the roles. -/
  ctor_role : ∀ {d c : DeclName} {fs : List FieldShape}, ctor d c fs →
    roles c = .constructor fs.length
  /-- The inductive types are the numbers, read with the tag of numbers, or declared
  datatypes, read with their own tags. -/
  inductivesRead : ∀ {T : DeclName} {cs : List (DeclName × List (Normalization.Field Tower.Head))},
    roles T = .inductive cs →
      (T = numN ∧ (reading.const T).Mem (.tag .nat)) ∨ (data T ∧ (reading.const T).Mem (.tag (.data T)))

namespace ObjectExtension

variable (X : ObjectExtension)

/-! ## Rigid types and weak-head reduction -/

/-- The rigid types of an extension: the object package's, with its declared datatypes. -/
def rigid : RigidTypes X.church :=
  objectRigidWith X.church X.sub X.data X.params X.ctor X.ctor_data X.zero_ctor X.suc_ctor

theorem roles_holds : X.roles holdsN = .computes 1 (.split 0 .constructor fun _ => .leaf) :=
  (X.roles_object (by decide)).trans objectRoles_holds

theorem roles_prop : X.roles propN = .rigid :=
  (X.roles_object (by decide)).trans objectRoles_propRigid

theorem roles_set : X.roles setN = .rigid :=
  (X.roles_object (by decide)).trans objectRoles_setRigid

/-- The ground types of the object package are weak-head normal under the extension's roles. -/
theorem ground_whnf {n : Nat} {g : CTm Tower.Head n} (hg : X.rigid.ground g) :
    Whnf X.rules X.roles g.erase := by
  rcases hg with rfl | rfl
  · exact constSpine_whnf X.shape (args := []) fun _ _ h => nomatch X.roles_set.symm.trans h
  · exact head_whnf X.shape _

/-- **The weak-head reduction of an extension**, under its roles. -/
def head : HeadReduction X.church X.rigid :=
  headReductionOf X.rigid X.roles X.shape X.deterministic X.roles_holds X.roles_prop
    X.data_role X.ctor_role X.ground_whnf

theorem head_step {n : Nat} {t u : CTm Tower.Head n} :
    X.head.step t u ↔ CWhStepR X.church X.roles t u :=
  Iff.rfl

/-! ## The universes and derivations of the object package -/

/-- `U_l` is a universe of the extension. -/
theorem sort (l : LevelExpr Nat) : X.rules.isUniverse (.sort l) :=
  X.sub.isUniverse (.sort l)

/-- A derivation of the object package is one of the extension. -/
theorem lift {J : CStatement Tower.Head} (derivation : CDerivable objectChurch J) :
    CDerivable X.church J :=
  derivation.mono X.sub

/-- A context formed in the object package is formed in the extension. -/
theorem liftFormed {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed objectChurch Γ) :
    CCtxFormed X.church Γ :=
  formed.mono X.sub

theorem soundnessFacts : SoundnessFacts X.reading X.church :=
  X.valid.soundnessFacts

/-- The join of two universe levels in the extension. -/
theorem join_sorts (l l' : LevelExpr Nat) :
    X.rules.join (.sort l) (.sort l') (.sort (.max l l')) :=
  X.sub.join (.sorts l l')

section Formation

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- `U_l` is a type of `U_(l+1)` in the extension. -/
theorem cU_typed (l : LevelExpr Nat) : CTyped X.church Γ (CU l) (CU (.succ l)) :=
  .headType (X.sub.headTyping (.sort l))

/-- A type of `U₀` is a type of `U₁`. -/
theorem craise {T : CTm Tower.Head n} (typed : CTyped X.church Γ T cU0) :
    CTyped X.church Γ T cU1 :=
  CDerivable.cumul typed (X.sub.cumulative
    (show objectRules.cumulative (.sort Tower.zero) (.sort (.succ Tower.zero)) from
      fun valuation => by simp [LevelExpr.eval, LevelTower.zero]))

theorem cpiT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped X.church Γ D (CU l)) (codomain : CTyped X.church (.snoc Γ D) B (CU l)) :
    CTyped X.church Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (X.sort l) codomain (X.sort l) (X.join_sorts l l))
    (X.sub.cumulative (show objectRules.cumulative (.sort (.max l l)) (.sort l) from
      fun valuation => by simp [LevelExpr.eval]))

theorem csigmaT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped X.church Γ D (CU l)) (codomain : CTyped X.church (.snoc Γ D) B (CU l)) :
    CTyped X.church Γ (.sigma D B) (CU l) :=
  CDerivable.cumul (.sigmaForm domain (X.sort l) codomain (X.sort l) (X.join_sorts l l))
    (X.sub.cumulative (show objectRules.cumulative (.sort (.max l l)) (.sort l) from
      fun valuation => by simp [LevelExpr.eval]))

theorem cidT {C a b : CTm Tower.Head n} {l : LevelExpr Nat}
    (carrier : CTyped X.church Γ C (CU l)) (left : CTyped X.church Γ a C)
    (right : CTyped X.church Γ b C) : CTyped X.church Γ (.id C a b) (CU l) :=
  .idForm carrier (X.sort l) left right

/-- The successor of a number is a number. -/
theorem csuc_typed {a : CTm Tower.Head n} (ta : CTyped X.church Γ a cnum) :
    CTyped X.church Γ (csuc a) cnum :=
  .appElim (B := cnum) (X.lift csucConst_typed) ta

/-- The sum of two numbers is a number. -/
theorem cadd_typed {a b : CTm Tower.Head n} (ta : CTyped X.church Γ a cnum)
    (tb : CTyped X.church Γ b cnum) : CTyped X.church Γ (cadd a b) cnum :=
  .appElim (B := cnum) (.appElim (B := .pi cnum cnum) (X.lift caddConst_typed) ta) tb

end Formation

/-! ## The conditions of the fundamental lemma -/

/-- **The heads typed by a head are universes or rigid ground types.** -/
theorem groundHeads : X.rigid.GroundHeads X.reading := by
  intro h u typing
  cases X.headTyping typing with
  | legacyGround => exact .inr ⟨by rw [X.reading_head]; rfl, fun {_} => .inr rfl⟩
  | sort l => exact .inl (X.sort l)

/-- The decoder applied to a head is a weak-head normal form under the extension's roles: a
root redex accepts a canonical code, and a head is not canonical. -/
theorem holds_head_whnf {n : Nat} (h : Tower.Head) :
    Whnf X.rules X.roles (.app (.const holdsN) (.head h) : Tower.Tm n) := by
  intro u step
  generalize ht : (Tm.app (.const holdsN) (.head h) : Tower.Tm n) = t at step
  cases step with
  | beta => cases ht
  | fstPair => cases ht
  | sndPair => cases ht
  | fst => cases ht
  | snd => cases ht
  | appFun s =>
      injection ht with _ hf _
      subst hf
      exact partialSpine_whnf X.shape X.roles_holds (args := []) Nat.zero_lt_one _ s
  | root s =>
      subst ht
      obtain ⟨c, arity, inspect, args, role, e, -, accepts⟩ := X.shape.spine s
      have e' : Normalization.appSpine (.const holdsN) [(.head h : Tower.Tm n)] =
          Normalization.appSpine (.const c) args := e
      obtain ⟨rfl, rfl⟩ := Normalization.appSpine_const_injective e'
      rw [X.roles_holds] at role
      injection role with _ hinspect
      subst hinspect
      obtain ⟨a, found, canonical⟩ := InspectTree.accepts_single.1 accepts
      obtain rfl : a = .head h := (Option.some.inj found).symm
      rcases canonical with ⟨x, hx⟩ | ⟨k, arity', args', -, hk⟩
      · cases hx
      · rcases appSpine_const_cases k args' with e₁ | ⟨f, b, e₁⟩
        · rw [e₁] at hk; cases hk
        · rw [e₁] at hk; cases hk
  | scrutinee role length focus inner =>
      have e : Normalization.appSpine (.const _) _ = Normalization.appSpine (.const holdsN)
          [(.head h : Tower.Tm n)] := ht.symm
      obtain ⟨rfl, rfl⟩ := Normalization.appSpine_const_injective e
      rw [X.roles_holds] at role
      injection role with harity hinspect
      subst harity hinspect
      obtain ⟨before, after, hb, hv, -, -⟩ := InspectTree.Focus.single focus
      rw [List.length_eq_zero_iff] at hb
      subst hb
      injection hv with ha _
      subst ha
      exact head_whnf X.shape h _ inner

/-- **The decoder is stuck at universes.** -/
theorem decoderStuck : X.head.DecoderStuckAtUniverses := by
  intro n h _ u step
  exact X.holds_head_whnf h _ (CWhStepR.erase step)

/-- **Neutral types take no head step.** -/
theorem neutralNormal : X.head.NeutralNormal X.roles :=
  fun neutral u => CWhStepR.not_of_whnf (Neutral.whnf X.shape neutral) u

/-- **The inductive types are read with their datatype's tag.** -/
theorem rigid_inductivesRead : X.rigid.InductivesRead X.roles X.reading :=
  fun role => X.inductivesRead role

/-- **The fundamental lemma within adequate constants of the object package**: a statement
derivable in the object package within allowed constants, all adequate in the extension, is
valid over a context formed in the extension. -/
theorem valid_within {allowed : DeclName → Bool}
    (consts : ∀ {c : DeclName}, allowed c = true → ConstAdequateAt X.reading X.head c)
    {J : CStatement Tower.Head} (derivation : CDerivable (objectChurch.restrict allowed) J)
    (formed : J.CtxFormed X.church) : J.Valid X.reading X.head :=
  CDerivable.valid_sub X.levels X.valid X.groundHeads X.groundHeadEq X.decoderStuck
    (ChurchRules.restrict_sub.trans X.sub)
    (fun declared => consts (ChurchRules.restrict_declared declared).1) derivation formed

/-! ## The reading of the object package's terms -/

/-- **A term of the object package's constants is read as the object reading reads it.** -/
theorem cinterp_eq {n : Nat} (t : CTm Tower.Head n)
    (h : ∀ c ∈ termConsts t, (objectRules.constantType c).isSome = true) :
    cinterp X.reading t = cinterp objectChurchReading t :=
  cinterp_congr X.reading_head t fun c hc => X.reading_const (h c hc)

theorem reading_num : X.reading.const numN = Ideal.natI := by
  rw [X.reading_const (by decide), objectChurchReading_num]

theorem reading_zero : X.reading.const zeroN = Ideal.zeroI := by
  rw [X.reading_const (by decide), objectChurchReading_zero]

theorem reading_set : X.reading.const setN = Ideal.groundI := by
  rw [X.reading_const (by decide), objectChurchReading_set]

theorem reading_prop : X.reading.const propN = Ideal.codesIdeal := by
  rw [X.reading_const (by decide), objectChurchReading_prop]

theorem cinterp_cnum {n : Nat} (ρ : Env n) : cinterp X.reading cnum ρ = Ideal.natI :=
  X.reading_num

/-- The simple types are read as the object reading reads them. -/
theorem cinterp_objectTypeAt (type : HOL.Ty SetProfile.SetBase) {n : Nat} (ρ : Env n) :
    cinterp X.reading (liftTm (FormationSensitiveHOLInterface.typeAt SetProfile.types n type)) ρ =
      simpleI type :=
  cinterp_typeAt X.reading_prop X.reading_num X.reading_set type ρ

/-- The identity eliminator's declared type mentions no constant, so it is read alike. -/
theorem jTypeI_eq (u : Tower.Head) : jTypeI X.reading u = jTypeI objectChurchReading u :=
  congrFun (cinterp_congr X.reading_head (jTypeC u) fun c hc => by
    simp [jTypeC, termConsts] at hc) Env.nil

/-- The identity eliminator is read as its function at the reflexivity point. -/
theorem reading_j : X.reading.const jName = jAlignedConst X.reading (.sort Tower.zero) := by
  rw [X.reading_const (by decide), objectChurchReading_j]
  unfold jAlignedConst
  rw [X.jTypeI_eq]

/-- A definition by one equation of the object package's constants is read alike. -/
theorem defConst_eq {k : Nat} (Θ : CCtx Tower.Head k) (T E : CTm Tower.Head k)
    (hT : ∀ c ∈ termConsts (pisCtx Θ T), (objectRules.constantType c).isSome = true)
    (hE : ∀ c ∈ termConsts (lamsCtx Θ E), (objectRules.constantType c).isSome = true) :
    defConst X.reading Θ T E = defConst objectChurchReading Θ T E := by
  unfold defConst
  rw [X.cinterp_eq _ hT, X.cinterp_eq _ hE]

/-! ## Scrutinee congruences of the object package's computing constants -/

section Scrutinees

variable {n : Nat}

/-- **The path of the identity eliminator**: `J A x M d y q ⟶ J A x M d y q'`. -/
theorem head_jPath {A x M d y q q' : CTm Tower.Head n} (s : X.head.step q q') :
    X.head.step (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q)
      (.app (CTm.appSpine (.const jName) [A, x, M, d, y]) q') := by
  have h := CWhStepR.scrutinee (before := [A, x, M, d, y]) (after := [])
    ((X.roles_object (by decide)).trans (objectRoles_of_roles roles_j nofun)) rfl s
  rw [CTm.appSpine_concat, CTm.appSpine_concat] at h
  exact h

/-- **The numeral of `num-rec`**: `num-rec P z s q ⟶ num-rec P z s q'`. -/
theorem head_numRec {P z s q q' : CTm Tower.Head n} (step : X.head.step q q') :
    X.head.step (.app (CTm.appSpine (.const numRecName) [P, z, s]) q)
      (.app (CTm.appSpine (.const numRecName) [P, z, s]) q') := by
  have h := CWhStepR.scrutinee (before := [P, z, s]) (after := [])
    ((X.roles_object (by decide)).trans (objectRoles_of_roles roles_numRec nofun)) rfl step
  rw [CTm.appSpine_concat, CTm.appSpine_concat] at h
  exact h

/-- **The numeral of addition**, its second argument: `add m q ⟶ add m q'`. -/
theorem head_add {m q q' : CTm Tower.Head n} (step : X.head.step q q') :
    X.head.step (.app (.app (.const addN) m) q) (.app (.app (.const addN) m) q') :=
  CWhStepR.scrutinee (before := [m]) (after := [])
    ((X.roles_object (by decide)).trans objectRoles_add) rfl step

/-- **The numeral of the iterated power set**, its first argument: `pow q X ⟶ pow q' X`. -/
theorem head_pow {q q' A : CTm Tower.Head n} (step : X.head.step q q') :
    X.head.step (.app (.app (.const powN) q) A) (.app (.app (.const powN) q') A) :=
  CWhStepR.scrutinee (before := []) (after := [A])
    ((X.roles_object (by decide)).trans objectRoles_pow) rfl step

/-- **The numeral of the iterator**, its first argument. -/
theorem head_iter {q q' A P st x h : CTm Tower.Head n} (step : X.head.step q q') :
    X.head.step (CTm.appSpine (.const iterName) [q, A, P, st, x, h])
      (CTm.appSpine (.const iterName) [q', A, P, st, x, h]) :=
  CWhStepR.scrutinee (before := []) (after := [A, P, st, x, h])
    ((X.roles_object (by decide)).trans (objectRoles_of_roles roles_iter nofun)) rfl step

end Scrutinees

end ObjectExtension

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
