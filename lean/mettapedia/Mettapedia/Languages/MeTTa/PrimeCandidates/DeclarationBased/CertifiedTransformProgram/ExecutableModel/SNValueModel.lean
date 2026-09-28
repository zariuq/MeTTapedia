import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNTransport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines

/-!
# The transport value model on the skeleton-free value side

Route T's consistency model `tmodelC`, its daimon and the object package as its
realizer side, read by model S over the skeleton-free value side with levels in
the natural numbers (`vmodel`):

* its laws are those of `tmodelC` with the daimon rigid and the constructors of
  the numbers declared (`vmodel_laws`);
* its reduction, roles and levels are those of `tmodelC`, which has the
  transport table, so the rows of the table hold (`vmodel_coeRules`);
* its reading of codes is the candidate reading of the object package
  (`vmodel_reading_eq`), since the numerals of the two sides agree;
* the program's codes are read by it (`vprogramCodes_readS`).

## Root steps

Every root step of a stage of the executable package without identity
elimination is a step of the model's reduction, so it preserves meaning, and a
stage whose constants are valid is sound (`vstage_soundS`).

Identity elimination is different. On the value side it transports its method
along the motive, `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`, while the
object package computes by its linear rule `J A x P d y (refl z) ⟶ d`, which
does not compare `x`, `y` and `z`. The root obligation of model S reads a root
step without its typing: its two sides must be validly equal wherever each is a
valid term of one type. At `J U2 U1 (λ y _. y) num U0 (refl U0)`, whose motive
sends the point `U1` and the endpoint `U0` to themselves, both sides are valid
terms of `U0`: the transport from `U1` into `U0` is stuck on the daimon, a
valid type, and realized by the strongly normalizing object term, while the
method `num` is a type of `U0`. They are not equal: the daimon's pack is not
the numbers' pack (`vmodel_mismatchJ_not_equal`). So the linear rule's root
obligation fails (`vmodel_jRoot_not_semantic`), and the object package is not
sound for the model as the fundamental lemma states soundness
(`objectRules_not_soundS_vmodel`). The redex is no typed term: `refl U0` is no
path from `U1`. Validating the object package's identity elimination needs the
typing of its path; read with the typing facts of its redexes the rule holds,
and the object package is sound (`SNValueSound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World Morph Carrier Kind CodesRead)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open Mettapedia.Logic
open Package (U0 numT jName)

namespace CodeModel

/-! ## The model -/

/-- **The transport value model on the skeleton-free value side**: route T's
consistency model, with its levels in the natural numbers, the daimon, and the
object package as the realizer side. -/
def vmodel (v : Nat → Nat) : ModelS.SModel Tower.Head Nat where
  toModel := tmodelC v
  star := starN
  realizers := objectRealizers

variable (v : Nat → Nat)

/-- **The laws of the model**: those of route T's consistency model, the daimon
rigid, and the constructors of the numbers declared as constructors. -/
theorem vmodel_laws : (vmodel v).Laws where
  values := tmodelC_laws v
  star := tmodelRoles_star
  starNotProp := by change starN ≠ propN; decide
  starNotHolds := by change starN ≠ holdsN; decide
  declared := tmodelConstructorsDeclared

/-- The laws of the model's value side. -/
theorem vmodel_valueLaws : (vmodel v).value.Laws :=
  (vmodel_laws v).value

theorem vmodel_rules : (vmodel v).rules = (tmodelC v).rules := rfl
theorem vmodel_roles : (vmodel v).roles = (tmodelC v).roles := rfl
theorem vmodel_level : (vmodel v).levels.level = (tmodelC v).levels.level := rfl

/-! ## The transport table -/

/-- **The transport table holds in the model**: route T's consistency model has
the transport table (`tmodel_coeTable`), and the numbers are its only inductive
type. -/
theorem vmodel_coeRules : ValueSide.CoeRules (vmodel v).value coeN :=
  (tmodel_coeTable v).coeRules (V := (vmodel v).value) (vmodel_valueLaws v)
    fun role => (tmodelRoles_inductive role).1

/-! ## The reading -/

/-- The numbers of the realizer side are the constructors `zero` and `suc`. -/
theorem objectRoles_num_ctors :
    objectRealizers.roles numN =
      .inductive [(objectRealizers.zero, []), (objectRealizers.suc, [.recursive])] :=
  objectRoles_num

/-- **The model reads codes by the candidate reading**: the reading of the
algebra of Kripke candidates is the candidate reading of the object package,
since the numerals of the value side and of the realizer side agree. -/
theorem vmodel_reading_eq :
    (vmodel v).reading =
      Realizability.candidateReading (tmodelC v).toSetting starN objectRealizers :=
  ModelS.kcandReading_eq objectRealizers (tmodelC v).toSetting starN numN rfl rfl
    objectRoles_num_ctors

/-! ## The program's codes -/

/-- A rigid constant of the consistency model other than the decoder is rigid in
the object package. -/
theorem objectRoles_of_modelRoles {T : DeclName} (role : modelRoles T = .rigid)
    (notHolds : T ≠ holdsN) : objectRoles T = .rigid := by
  have hj : T ≠ jName := by
    intro e
    rw [e] at role
    change (if jName = jName then Role.computes 6 .leaf else _) = _ at role
    rw [if_pos rfl] at role
    cases role
  have hi : T ≠ impN := by
    intro e
    rw [e] at role
    change (if impN = jName then Role.computes 6 .leaf else
      if impN = impN then Role.constructor 2 else _) = _ at role
    rw [if_neg (by decide), if_pos rfl] at role
    cases role
  cases ha : SetProfile.allInstance? T with
  | some _ =>
      unfold modelRoles at role
      rw [if_neg hj, if_neg hi, ha] at role
      cases role
  | none =>
      cases he : SetProfile.eqInstance? T with
      | some _ =>
          unfold modelRoles at role
          rw [if_neg hj, if_neg hi, ha] at role
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, he, Option.isSome_some,
            if_true] at role
          cases role
      | none =>
          rw [objectRoles_of notHolds hi ha he, ← modelRoles_of hj hi ha he]
          exact role

/-- A rigid constant of the transport value model other than the decoder is
rigid in the object package. -/
theorem objectRoles_of_tmodelRoles {T : DeclName} (role : tmodelRoles T = .rigid)
    (notHolds : T ≠ holdsN) : objectRoles T = .rigid := by
  by_cases fresh : T ∈ coeNameList
  · exfalso
    simp only [coeNameList, List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [tmodelRoles_coe] at role; cases role
    · rw [tmodelRoles_coeU] at role; cases role
    · rw [tmodelRoles_coeNum] at role; cases role
    · rw [tmodelRoles_coeProp] at role; cases role
    · rw [tmodelRoles_coePi] at role; cases role
    · rw [tmodelRoles_coeSigma] at role; cases role
  · rw [tmodelRoles_eq fresh] at role
    exact objectRoles_of_modelRoles role notHolds

/-- The carrier of every simple type is interpreted by route T's consistency
model. -/
theorem tcarrierOf_interpretable :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.Interpretable (tmodelC v)
  | .prop => .prop
  | .base .num => .num
  | .base .set =>
      .rigid ((tmodelRoles_eq (by decide)).trans ((modelRoles_of (name := setN) (by decide)
        (by decide) (by decide) (by decide)).trans roles_set))
        (by change setN ≠ propN; decide) (by change setN ≠ holdsN; decide)
  | .arr a b => .arr (tcarrierOf_interpretable a) (tcarrierOf_interpretable b)

/-- The carrier of a simple type, as a type of the package, is the profile's
type. -/
theorem tcarrierOf_term :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.term (tmodelC v) = typeTerm type
  | .prop => rfl
  | .base .num => rfl
  | .base .set => rfl
  | .arr a b => by
      have ha := tcarrierOf_term a
      have hb := tcarrierOf_term b
      simp only [carrierOf, Consistency.Carrier.term, typeTerm,
        Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface.typeAt]
        at ha hb ⊢
      rw [ha, hb,
        Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface.typeAt_rename]

/-- The program's codes are read by route T's consistency model. -/
theorem tprogramCodes_read : CodesRead (tmodelC v) programCodes where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := by
    intro a T found
    change (SetProfile.allInstance? a).map typeTerm = some T at found
    cases found' : SetProfile.allInstance? a with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, tcarrierOf_interpretable v type,
          (tcarrierOf_term v type).symm⟩
        change (SetProfile.allInstance? a).map carrierOf = _
        rw [found']
        rfl
  eq := by
    intro e T found
    change (SetProfile.eqInstance? e).map typeTerm = some T at found
    cases found' : SetProfile.eqInstance? e with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, tcarrierOf_interpretable v type,
          (tcarrierOf_term v type).symm⟩
        change (SetProfile.eqInstance? e).map carrierOf = _
        rw [found']
        rfl

/-- The closed type of every carrier interpretable by the transport value model
is strongly normalizing in the object package. -/
theorem tcarrier_sn : ∀ {k : Kind} {C : Carrier k},
    C.Interpretable (tmodelC v) → SN objectRules (C.term (tmodelC v))
  | _, _, .prop => const_sn fun _ _ role => by
      change objectRoles propN = _ at role
      rw [objectRoles_prop] at role
      cases role
  | _, _, .num => const_sn fun _ _ role => by
      change objectRoles numN = _ at role
      rw [objectRoles_num] at role
      cases role
  | _, _, .rigid role _ notHolds => const_sn fun _ _ role' => by
      rw [objectRoles_of_tmodelRoles role notHolds] at role'
      cases role'
  | _, _, .arr dom cod =>
      SN.pi (RootShape.spineHeaded objectShape) (tcarrier_sn dom)
        (SN.rename objectReflects wk (tcarrier_sn cod))

/-- The program's codes are read by the model. -/
theorem vprogramCodes_readS : ModelS.CodesReadS (vmodel v) programCodes where
  read := tprogramCodes_read v
  decoders := rfl
  propStuck := fun arity scrutinee role => by
    change objectRoles propN = _ at role
    rw [objectRoles_prop] at role
    cases role
  carrierSN := fun hC => tcarrier_sn v hC

/-- The decoders of the program's codes are the codes of the model. -/
theorem vprogramDecodes : Consistency.Decodes (vmodel v).toModel programCodes.decoders :=
  (tprogramCodes_read v).decodes

/-! ## Stages without identity elimination -/

/-- **A root step of a stage without identity elimination is a step of the
model's reduction**: the computations of the package other than identity
elimination are computations of the transport value model. -/
theorem vmodel_step_of_stage {allowed : DeclName → Bool} (noJ : allowed jName = false)
    {n : Nat} {l r : Tower.Tm n} (step : (stage allowed).computation.step l r) :
    (vmodel v).rules.computation.step l r := by
  change (RootComputation.unionAll (computations.filter fun entry => allowed entry.1)).step l r
    at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  obtain ⟨listedIn, allowedIn⟩ := List.mem_filter.mp mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tmodel_step v (tmodelListed v 0 (by decide)) h
  · exact tmodel_step v (tmodelListed v 1 (by decide)) h
  · exact tmodel_step v (tmodelListed v 2 (by decide)) h
  · rw [noJ] at allowedIn
    cases allowedIn
  · exact tmodel_step v (tmodelListed v 4 (by decide)) h
  · exact tmodel_step v (tmodelListed v 5 (by decide)) h
  · exact tmodel_step v (tmodelListed v 6 (by decide)) h
  · exact tmodel_step v (tmodelListed v 7 (by decide)) h
  · exact tmodel_step v (tmodelListed v 8 (by decide)) h
  · exact tmodel_step v (tmodelListed v 9 (by decide)) h
  · exact tmodel_step v (tmodelListed v 10 (by decide)) h
  · exact tmodel_step v (tmodelListed v 11 (by decide)) h

/-- **A stage without identity elimination whose constants are valid is sound
for the model**: its root steps are steps of the model's reduction. -/
theorem vstage_soundS {allowed : DeclName → Bool} (noJ : allowed jName = false)
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ModelS.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelS.TypedSoundS (stage allowed) (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => .inl (ModelS.ModelRootS.semantic (vmodel_laws v) (vprogramDecodes v)
    (.inl (vmodel_step_of_stage v noJ step)))
  constants := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    split_ifs at declared with h
    exact constants h declared

/-- A stage of the listed names, without identity elimination, whose constants
are valid is sound for the model. -/
theorem vstage_soundS_of {names : List DeclName} (noJ : jName ∉ names)
    (constants : ∀ name ∈ names, ∀ {type : Tower.Tm 0}, allTypes name = some type →
      ModelS.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelS.TypedSoundS (stage (allowedIn names)) (vmodel v) :=
  vstage_soundS v (by simpa [allowedIn] using noJ) fun {name _} allowed declared =>
    constants name (by simpa [allowedIn] using allowed) declared

/-! ## The linear rule of identity elimination

The obstruction: the object package's identity elimination at a path whose
endpoints the linear rule does not compare. -/

/-- The motive `λ y _. y`: the endpoint itself, as a type. -/
abbrev endpointMotive {n : Nat} : Tower.Tm n := .lam (.lam (.var 1))

/-- Identity elimination with the motive `λ y _. y` from the point `U1` along
`refl U0` to the endpoint `U0`, with the method `num`. The linear rule of the
object package fires at it, while `refl U0` is no path from `U1`. -/
def mismatchJ {n : Nat} : Tower.Tm n :=
  appSpine (.const jName)
    [sortTm (.succ (.succ Tower.zero)), U1, endpointMotive, numT, U0, .refl U0]

theorem subst_mismatchJ {n m : Nat} (σ : Sub Tower.Head n m) :
    Presentation.subst σ (mismatchJ : Tower.Tm n) = mismatchJ :=
  rfl

theorem rename_mismatchJ {n m : Nat} (ρ : Ren n m) :
    Presentation.rename ρ (mismatchJ : Tower.Tm n) = mismatchJ :=
  rfl

/-- **The object package computes `mismatchJ` to its method** by the linear rule
of identity elimination. -/
theorem objectStep_mismatchJ {n : Nat} :
    objectRules.computation.step (mismatchJ : Tower.Tm n) numT :=
  .inl (rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩)

/-- The motive `λ y _. y` at a type and any path computes the type. -/
theorem endpointMotive_red {n : Nat} (y e : Tower.Tm n) (u : Tower.Head) (hy : y = .head u) :
    WhRed (vmodel v).rules (vmodel v).roles (.app (.app endpointMotive y) e) (.head u) := by
  subst hy
  exact .head (.appFun (.beta _ _)) (.single (.beta _ _))

/-- **On the value side `mismatchJ` is stuck on the daimon**: identity
elimination transports `num` from the motive at the point, `U1`, into the motive
at the endpoint, `U0`, and a transport into a universe from a universe of a
higher level is stuck on the daimon. -/
theorem vmodel_mismatchJ_red {n : Nat} :
    ∃ w, WhRed (vmodel v).rules (vmodel v).roles (mismatchJ : Tower.Tm n) w ∧
      Daimonic (vmodel v).roles (vmodel v).star w := by
  have rY := endpointMotive_red (v := v) (U0 : Tower.Tm n) (.refl U0) (.sort (.const 0)) rfl
  have rX :=
    endpointMotive_red (v := v) (U1 : Tower.Tm n) (.refl U1) (.sort (.succ Tower.zero)) rfl
  obtain ⟨w, rw, dw⟩ := (vmodel_coeRules v).univOther (d := numT) rY (Tower.IsUniverse.sort _)
    rX (.inl ⟨_, rfl, Tower.IsUniverse.sort _⟩)
    (fun u' e _ => by
      cases e
      exact Nat.zero_lt_one)
  exact ⟨w, .head (tmodel_j_step v _ _ _ _ _ _) rw, dw⟩

/-- The type of the numbers does not compute in the object package. -/
theorem numT_sn {n : Nat} : SN objectRules (numT : Tower.Tm n) :=
  const_sn fun _ _ role => by
    change objectRoles numN = _ at role
    rw [objectRoles_num] at role
    cases role

/-- The object term `mismatchJ` is strongly normalizing: its arguments are, and
it computes only at reflexivity, to its method. -/
theorem mismatchJ_sn {n : Nat} : SN objectRules (mismatchJ : Tower.Tm n) := by
  have spine := RootShape.spineHeaded objectShape
  have role : objectRoles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
    (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_j
  exact KCand.eliminator_mem objectShape objectReflects (KCand.sn' objectReflects) role
    objectStep_j (Q := True) (SN.head spine _) (SN.head spine _)
    (SN.lam spine (SN.lam spine (SN.var spine _))) numT_sn (SN.head spine _)
    ⟨SN.refl spine (SN.head spine _), fun _ _ => trivial⟩ (fun _ => numT_sn)

/-- `mismatchJ` is a type of every level, by the pack of daimonic types. -/
theorem vmodel_mismatchJ_interp (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ mismatchJ (ValueSide.Pack.total (vmodel v).value n) ∧
      ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ
        mismatchJ mismatchJ := by
  obtain ⟨w, red, daimonic⟩ := vmodel_mismatchJ_red (v := v) (n := n)
  have interp : ValueSide.InterpAt (vmodel v).value l ξ mismatchJ
      (ValueSide.Pack.total (vmodel v).value n) :=
    ValueSide.SInterp.daimon red daimonic
  have total := ValueSide.Shape.of_daimonic (vmodel_valueLaws v) interp red daimonic
  exact ⟨interp, .total total total⟩

/-- **`mismatchJ` is a valid term of `U0`**: at every world it is a daimonic
type, of one shape with itself, and its object term is strongly normalizing. -/
theorem vmodel_mismatchJ_valid : ModelS.ValidTmS (vmodel v) .nil mismatchJ U0 := by
  refine ⟨ModelS.ValidTyS.sort (Tower.IsUniverse.sort _), fun {_ _ ξ σ σ' ς} _ {P} den => ?_⟩
  rw [ModelS.DenS.sort_inv (vmodel_laws v) (Tower.IsUniverse.sort _) den]
  rw [subst_mismatchJ, subst_mismatchJ, subst_mismatchJ]
  refine ⟨fun {_ ξ' ρ} _ => ?_, mismatchJ_sn⟩
  rw [rename_mismatchJ]
  obtain ⟨interp, shape⟩ := vmodel_mismatchJ_interp (v := v) _ ξ'
  exact ⟨_, interp, interp, shape⟩

/-- **The numbers are a valid term of `U0`**: at every world they are
interpreted at the lowest level by their inductive pack, of one shape with
themselves, and the constant is strongly normalizing. -/
theorem vmodel_valid_num : ModelS.ValidTmS (vmodel v) .nil (.const numN) U0 := by
  have laws := vmodel_valueLaws v
  refine ⟨ModelS.ValidTyS.sort (Tower.IsUniverse.sort _), fun {_ _ ξ σ σ' ς} _ {P} den => ?_⟩
  rw [ModelS.DenS.sort_inv (vmodel_laws v) (Tower.IsUniverse.sort _) den]
  refine ⟨fun {_ ξ' ρ} _ => ?_, numT_sn⟩
  exact ⟨_, ValueSide.InterpAt.num laws _ .refl, ValueSide.InterpAt.num laws _ .refl,
    .const (.inr ⟨_, laws.num_role⟩) .refl .refl⟩

/-- **`mismatchJ` and its method are not validly equal at `U0`**: in the closed
world the universe relates them only if they have one pack, while `mismatchJ`
has the pack of daimonic types and the numbers have their inductive pack, which
does not relate `zero` to `suc zero`. -/
theorem vmodel_mismatchJ_not_equal : ¬ ModelS.ValidEqS (vmodel v) .nil mismatchJ numT U0 := by
  intro equal
  have laws := vmodel_valueLaws v
  let empty : Sub Tower.Head 0 0 := fun i => Fin.elim0 i
  have den : ValueSide.DenS (vmodel v).value World.closed (Presentation.subst empty U0)
      (ModelS.universeAt (vmodel v) 0 World.closed) :=
    ValueSide.DenS.sort (V := (vmodel v).value) (Tower.IsUniverse.sort _) World.closed
  obtain ⟨Q, hl, hr, -⟩ :=
    equal.2.2 (σ := empty) (σ' := empty) (ς := empty) trivial den (Morph.id World.closed)
  change ValueSide.InterpAt (vmodel v).value 0 World.closed mismatchJ Q at hl
  change ValueSide.InterpAt (vmodel v).value 0 World.closed numT Q at hr
  obtain rfl := hl.deterministic laws (vmodel_mismatchJ_interp (v := v) 0 World.closed).1
  have num := hr.deterministic laws (ValueSide.InterpAt.num laws 0 .refl)
  have related₀ : (ValueSide.numIndPack (vmodel v).value 0).rel (.const zeroN)
      (.app (.const sucN) (.const zeroN)) := by
    rw [← num]
    trivial
  obtain ⟨s, hz, hs⟩ := ValueSide.numIndPack_rel.mp related₀
  have zero := Realizability.HasShape.deterministic laws.values.truth laws.star hz (.zero .refl)
  have suc := Realizability.HasShape.deterministic laws.values.truth laws.star hs
    (.suc .refl (.zero .refl))
  rw [zero] at suc
  cases suc

/-- **The root obligation of the linear rule of identity elimination fails in
the model**: at `mismatchJ` both sides of the object package's step are valid
terms of `U0`, and they are not validly equal. -/
theorem vmodel_jRoot_not_semantic :
    ¬ ModelS.RootSemanticS (vmodel v) (mismatchJ : Tower.Tm 0) numT :=
  fun semantic => vmodel_mismatchJ_not_equal v
    (semantic (vmodel_mismatchJ_valid v) (vmodel_valid_num v))

/-- **The object package is not sound for the model**: the linear rule of
identity elimination is one of its root steps, and its root obligation fails at
`mismatchJ`. -/
theorem objectRules_not_soundS_vmodel : ¬ ModelS.SoundS objectRules (vmodel v) :=
  fun sound => vmodel_jRoot_not_semantic v (sound.2 objectStep_mismatchJ)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
