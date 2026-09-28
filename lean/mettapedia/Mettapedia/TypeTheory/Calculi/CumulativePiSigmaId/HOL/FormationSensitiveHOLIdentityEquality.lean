import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AlgebraicParallel

/-!
# Identity interpretation of represented equality

The identity interpretation reads a represented equation `eq@T a b` of a
declared HOL interface as native identity on the interpreted carrier: the
proof family at `eq@T a b` computes to `Id T a b`.  It is a declared extension
of a rules package, with one decoding equation and no constant.

It is not equality reflection.  Identity evidence does not make its endpoints
convertible, and no conversion identifies two terms because an equation
between them is provable.

`decode` reads a represented formula as a dependent type: implication and
universal quantification as dependent functions, equations as identity types,
and every other proposition as its proof family.  In a host with the two
proof-family decoders and the equation decoder, the proof family at a
represented formula computes to its reading (`decodes`).  In every host of the
proof family, decoding an equation preserves typing, and native reflexivity
realizes `∀ x. eq x x`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLIdentityEquality

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence Presentation.AlgebraicParallel
open FormationSensitiveHOLInterface FormationSensitiveHOLGenericProofFamily
  FormationSensitiveHOLGenericProofPreservation Mettapedia.Logic

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The equality of an interface is a declared constant at each type. -/
structure DeclaredEquality (source : LogicalSignature Base Const) where
  equalityName : HOL.Ty Base → DeclName
  equality_eq : ∀ type, source.equality type = .const (equalityName type)
  equality_lookup : ∀ type, source.rules.constantType (equalityName type) =
    some (typeAt source.types 0 (.arr type (.arr type .prop)))

/-- The represented equation `eq@T left right`. -/
def equation (source : LogicalSignature Base Const) (type : HOL.Ty Base) {n : Nat}
    (left right : Tower.Tm n) : Tower.Tm n :=
  .app (.app (liftClosed (source.equality type)) left) right

@[simp] theorem equation_rename (source : LogicalSignature Base Const) (type : HOL.Ty Base)
    {n m : Nat} (ρ : Ren n m) (left right : Tower.Tm n) :
    Presentation.rename ρ (equation source type left right) =
      equation source type (Presentation.rename ρ left) (Presentation.rename ρ right) := by
  simp only [equation, Presentation.rename, rename_liftClosed]

@[simp] theorem equation_subst (source : LogicalSignature Base Const) (type : HOL.Ty Base)
    {n m : Nat} (σ : Sub Tower.Head n m) (left right : Tower.Tm n) :
    Presentation.subst σ (equation source type left right) =
      equation source type (Presentation.subst σ left) (Presentation.subst σ right) := by
  simp only [equation, Presentation.subst, subst_liftClosed]

/-! ## The equation decoder -/

/-- The proof family at a represented equation is the identity type on the
interpreted carrier. -/
inductive IdentityStep (source : LogicalSignature Base Const) (proofName : DeclName) :
    {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | equation {n : Nat} (type : HOL.Ty Base) (left right : Tower.Tm n) :
      IdentityStep source proofName (proof proofName (equation source type left right))
        (.id (typeAt source.types n type) left right)

def computation (source : LogicalSignature Base Const) (proofName : DeclName) :
    RootComputation Tower.Head where
  step := IdentityStep source proofName
  rename := by
    intro n m ρ left right step
    cases step with
    | equation type l r =>
        simpa only [proof_rename, equation_rename, Presentation.rename, typeAt_rename] using
          IdentityStep.equation (source := source) (proofName := proofName) type
            (Presentation.rename ρ l) (Presentation.rename ρ r)
  substitute := by
    intro n m σ left right step
    cases step with
    | equation type l r =>
        simpa only [proof_subst, equation_subst, Presentation.subst, typeAt_subst] using
          IdentityStep.equation (source := source) (proofName := proofName) type
            (Presentation.subst σ l) (Presentation.subst σ r)

/-- The interpretation adds the decoding equation and no constant. -/
def declarations (source : LogicalSignature Base Const) (proofName : DeclName) :
    Signature Tower.Head where
  entries := Signature.empty.entries
  computation := computation source proofName

/-- The identity interpretation of a rules package. -/
def interpret (base : Rules Tower.Head) (source : LogicalSignature Base Const)
    (proofName : DeclName) : Rules Tower.Head :=
  extendRules base (declarations source proofName)

theorem interpretMorphism (base : Rules Tower.Head) (source : LogicalSignature Base Const)
    (proofName : DeclName) :
    base.Morphism (interpret base source proofName) (fun head => head) :=
  includeMorphism base (declarations source proofName)

theorem interpret_decodes (base : Rules Tower.Head) (source : LogicalSignature Base Const)
    (proofName : DeclName) {n : Nat} {left right : Tower.Tm n}
    (step : IdentityStep source proofName left right) :
    (interpret base source proofName).computation.step left right :=
  RootStep.declared step

/-- The interpretation adds no constant: a program and its interpretation
declare the same constants. -/
theorem interpret_constantType (base : Rules Tower.Head) (source : LogicalSignature Base Const)
    (proofName : DeclName) (name : DeclName) :
    (interpret base source proofName).constantType name = base.constantType name := by
  change combinedType base (declarations source proofName) name = base.constantType name
  unfold combinedType
  split
  · next known => exact known.symm
  · next missing => rw [missing]; rfl

/-- Interpretation is functorial: a morphism of programs lifts to their
interpretations. -/
theorem interpret_map {base base' : Rules Tower.Head} (source : LogicalSignature Base Const)
    (proofName : DeclName) (map : base.Morphism base' (fun head => head)) :
    (interpret base source proofName).Morphism (interpret base' source proofName)
      (fun head => head) where
  headTyping := map.headTyping
  isUniverse := map.isUniverse
  join := map.join
  cumulative := map.cumulative
  headEq := map.headEq
  constantType := by
    intro name type known
    rw [interpret_constantType] at known ⊢
    exact map.constantType known
  computation := by
    intro n left right step
    cases step with
    | inherited inner =>
        have mapped := map.computation inner
        simp only [Tm.mapHead_id] at mapped ⊢
        exact RootStep.inherited mapped
    | delta lookup =>
        simp [Signature.valueOf?, declarations, Signature.empty] at lookup
    | declared decoded =>
        simp only [Tm.mapHead_id]
        exact RootStep.declared decoded

/-- Interpreted carriers are closed. -/
theorem variableMultiplicity_typeAt (types : TypeInterpretation Base) :
    ∀ (type : HOL.Ty Base) {n : Nat} (index : Fin n),
      AlgebraicSchema.variableMultiplicity index (typeAt types n type) = 0
  | .prop, _, index => AlgebraicSchema.variableMultiplicity_liftClosed _ index
  | .base _, _, index => AlgebraicSchema.variableMultiplicity_liftClosed _ index
  | .arr domain codomain, n, index => by
      simp only [typeAt, AlgebraicSchema.variableMultiplicity,
        variableMultiplicity_typeAt types domain index,
        variableMultiplicity_typeAt types codomain index.succ]

/-! ## Reading formulas as types -/

/-- The dependent reading of a represented formula. -/
def decode (source : LogicalSignature Base Const) (proofName : DeclName) :
    {gamma : HOL.Ctx Base} → {type : HOL.Ty Base} → HOL.Term Const gamma type →
      Option (Tower.Tm gamma.length)
  | _, _, .imp premise conclusion =>
      match decode source proofName premise, decode source proofName conclusion with
      | some p, some q => some (.pi p (Presentation.rename wk q))
      | _, _ => none
  | _, _, @HOL.Term.all _ _ type _ body =>
      (decode source proofName body).map (.pi (typeAt source.types _ type))
  | _, _, @HOL.Term.eq _ _ _ type left right =>
      match represent source left, represent source right with
      | some l, some r => some (.id (typeAt source.types _ type) l r)
      | _, _ => none
  | _, _, term => (represent source term).map (proof proofName)

/-- Whether a formula mentions an equation. -/
def mentionsEquation : {gamma : HOL.Ctx Base} → {type : HOL.Ty Base} →
    HOL.Term Const gamma type → Bool
  | _, _, .imp premise conclusion => mentionsEquation premise || mentionsEquation conclusion
  | _, _, .all body => mentionsEquation body
  | _, _, .eq _ _ => true
  | _, _, _ => false

/-- The proof family at a represented formula computes to its dependent
reading, in any host of the proof family that decodes equations whenever the
formula mentions one. -/
theorem decodes_core (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head)) :
    ∀ {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type),
      (mentionsEquation term = true → ∀ {n : Nat} {left right : Tower.Tm n},
        IdentityStep source proofName left right → R.computation.step left right) →
      ∀ {code decoded : Tower.Tm gamma.length},
      represent source term = some code → decode source proofName term = some decoded →
        StepStar R (proof proofName code) decoded := by
  have decoder : ∀ {n : Nat} {left right : Tower.Tm n},
      DecoderStep source proofName left right → StepStar R left right := by
    intro n left right step
    have mapped := host.computation (RootStep.declared step)
    simp only [Tm.mapHead_id] at mapped
    exact .single (.root mapped)
  intro gamma type term
  induction term with
  | var index =>
      intro _ code decoded represented decodedEq
      change (represent source (.var index)).map (proof proofName) = some decoded at decodedEq
      rw [represented] at decodedEq
      cases decodedEq
      exact .refl
  | const symbol =>
      intro _ code decoded represented decodedEq
      change (represent source (.const symbol)).map (proof proofName) = some decoded at decodedEq
      rw [represented] at decodedEq
      cases decodedEq
      exact .refl
  | app function argument _ _ =>
      intro _ code decoded represented decodedEq
      change (represent source (.app function argument)).map (proof proofName) = some decoded
        at decodedEq
      rw [represented] at decodedEq
      cases decodedEq
      exact .refl
  | lam body _ =>
      intro _ code decoded represented decodedEq
      change (represent source (.lam body)).map (proof proofName) = some decoded at decodedEq
      rw [represented] at decodedEq
      cases decodedEq
      exact .refl
  | top => intro _ code decoded represented; simp [represent] at represented
  | bot => intro _ code decoded represented; simp [represent] at represented
  | and _ _ _ _ => intro _ code decoded represented; simp [represent] at represented
  | or _ _ _ _ => intro _ code decoded represented; simp [represent] at represented
  | not _ _ => intro _ code decoded represented; simp [represent] at represented
  | ex _ _ => intro _ code decoded represented; simp [represent] at represented
  | imp premise conclusion premiseIH conclusionIH =>
      intro identity code decoded represented decodedEq
      have premiseIdentity : mentionsEquation premise = true →
          ∀ {n : Nat} {left right : Tower.Tm n},
            IdentityStep source proofName left right → R.computation.step left right :=
        fun mentioned => identity (by simp [mentionsEquation, mentioned])
      have conclusionIdentity : mentionsEquation conclusion = true →
          ∀ {n : Nat} {left right : Tower.Tm n},
            IdentityStep source proofName left right → R.computation.step left right :=
        fun mentioned => identity (by simp [mentionsEquation, mentioned])
      rw [FormationSensitiveHOLInterface.represent_imp] at represented
      cases hp : represent source premise with
      | none => simp [hp] at represented
      | some p =>
          cases hq : represent source conclusion with
          | none => simp [hp, hq] at represented
          | some q =>
              simp only [hp, hq] at represented
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at represented
              subst represented
              cases hdp : decode source proofName premise with
              | none => simp [decode, hdp] at decodedEq
              | some dp =>
                  cases hdq : decode source proofName conclusion with
                  | none => simp [decode, hdp, hdq] at decodedEq
                  | some dq =>
                      simp only [decode, hdp, hdq, Option.some.injEq] at decodedEq
                      subst decodedEq
                      exact .trans (decoder (.implication p q))
                        (stepStar_pi (premiseIH premiseIdentity hp hdp)
                          (stepStar_rename wk (conclusionIH conclusionIdentity hq hdq)))
  | @all quantified gamma' body bodyIH =>
      intro identity code decoded represented decodedEq
      rw [FormationSensitiveHOLInterface.represent_all] at represented
      cases hb : represent source body with
      | none => simp [hb] at represented
      | some b =>
          simp only [hb, Option.map_some, Option.some.injEq] at represented
          subst represented
          cases hdb : decode source proofName body with
          | none => simp [decode, hdb] at decodedEq
          | some db =>
              simp only [decode, hdb, Option.map_some, Option.some.injEq] at decodedEq
              subst decodedEq
              have beta : StepStar R
                  (proof proofName (.app (Presentation.rename wk (.lam b)) (.var 0)))
                  (proof proofName b) := by
                have step : Step R.headEq
                    (.app (.lam (Presentation.rename (liftRen wk) b)) (.var 0))
                    (inst0 (.var 0) (Presentation.rename (liftRen wk) b)) R.computation :=
                  .betaPi _ _
                rw [instantiate_shifted_body] at step
                exact .single (.congAppArg step)
              exact .trans (decoder (.universal quantified (.lam b)))
                (stepStar_pi .refl (beta.trans (bodyIH identity hb hdb)))
  | @eq gamma' compared left right _ _ =>
      intro identity code decoded represented decodedEq
      cases hl : represent source left with
      | none =>
          simp only [FormationSensitiveHOLInterface.represent, hl] at represented
          cases represented
      | some l =>
          cases hr : represent source right with
          | none =>
              simp only [FormationSensitiveHOLInterface.represent, hl, hr] at represented
              cases represented
          | some r =>
              rw [FormationSensitiveHOLInterface.represent_eq source left right hl hr] at represented
              cases represented
              simp only [decode, hl, hr, Option.some.injEq] at decodedEq
              subst decodedEq
              exact .single (.root (identity rfl (.equation compared l r)))

/-- In a host with the proof-family decoders and the equation decoder, the
proof family at a represented formula computes to its dependent reading. -/
theorem decodes (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head))
    (identity : ∀ {n : Nat} {left right : Tower.Tm n},
      IdentityStep source proofName left right → R.computation.step left right)
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type)
    {code decoded : Tower.Tm gamma.length}
    (represented : represent source term = some code)
    (decodedEq : decode source proofName term = some decoded) :
    StepStar R (proof proofName code) decoded :=
  decodes_core source proofName host term (fun _ => identity) represented decodedEq

/-- A formula without equations needs no equation decoder: its proof family
computes to its reading in every host of the proof family. -/
theorem decodes_equationFree (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head))
    {gamma : HOL.Ctx Base} {type : HOL.Ty Base} (term : HOL.Term Const gamma type)
    (free : mentionsEquation term = false) {code decoded : Tower.Tm gamma.length}
    (represented : represent source term = some code)
    (decodedEq : decode source proofName term = some decoded) :
    StepStar R (proof proofName code) decoded :=
  decodes_core source proofName host term
    (fun mentioned => absurd (mentioned.symm.trans free) (by decide)) represented decodedEq

/-! ## Decoding preserves typing -/

/-- Decoding an equation preserves every displayed type in any host that
receives the proof family and separates dependent functions. -/
theorem identityStep_preserves (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none) (equality : DeclaredEquality source)
    (universes : UniverseRegularity R) (boundary : PiConversionBoundary R)
    {n : Nat} {Γ : Tower.Ctx n} {left right displayed : Tower.Tm n}
    (formed : ContextFormation R Γ) (observed : Typing R Γ left displayed)
    (step : IdentityStep source proofName left right) : Typing R Γ right displayed := by
  cases step with
  | equation type l r =>
      obtain ⟨proposition, _, _, replay⟩ :=
        (proofSpine source proofName host fresh Γ).recoverApplication universes boundary
          formed observed
      have shape : equation source type l r =
          .app (.app (.const (equality.equalityName type)) l) r := by
        simp only [equation, equality.equality_eq, liftClosed, Presentation.rename]
      rw [shape] at proposition
      obtain ⟨_, _, inner, _, _, _⟩ := proposition.appGeneration
      obtain ⟨leftTyped, next, _⟩ := simpleArgument universes boundary formed
        (constantSpine source proofName host (equality.equality_lookup type) Γ) inner
      obtain ⟨rightTyped, _, _⟩ := simpleArgument universes boundary formed next proposition
      have carrier : Typing R Γ (typeAt source.types n type) (sortTm Tower.zero) :=
        host_typed source proofName host
          (include_typed source proofName (typeAt_formed source type Γ))
      exact replay (.idForm carrier (host.isUniverse (Tower.IsUniverse.sort Tower.zero))
        leftTyped rightTyped)

/-! ## Reflexivity -/

/-- `∀ x : T. eq x x`. -/
def reflexivity (type : HOL.Ty Base) : HOL.Formula Const [] :=
  HOL.Term.all (σ := type) (.eq (.var .vz) (.var .vz))

/-- The represented reflexivity principle. -/
def reflexivityCode (source : LogicalSignature Base Const) (type : HOL.Ty Base) : Tower.Tm 0 :=
  universalProposition source type (.lam (equation source type (.var 0) (.var 0)))

theorem reflexivity_represented (source : LogicalSignature Base Const) (type : HOL.Ty Base) :
    represent source (reflexivity (Const := Const) type) = some (reflexivityCode source type) :=
  rfl

/-- Native reflexivity realizes the reflexivity principle: `λ x. refl x`. -/
theorem refl_realizes (source : LogicalSignature Base Const) (proofName : DeclName)
    {R : Rules Tower.Head} (host : (rules source proofName).Morphism R (fun head => head))
    (fresh : source.rules.constantType proofName = none)
    (identity : ∀ {n : Nat} {left right : Tower.Tm n},
      IdentityStep source proofName left right → R.computation.step left right)
    (type : HOL.Ty Base) :
    Typing R .nil (.lam (.refl (.var 0))) (proof proofName (reflexivityCode source type)) := by
  have decoded : StepStar R (proof proofName (reflexivityCode source type))
      (.pi (typeAt source.types 0 type) (.id (typeAt source.types 1 type) (.var 0) (.var 0))) :=
    decodes source proofName host identity (reflexivity type) (reflexivity_represented source type)
      rfl
  have isSort : R.isUniverse (.sort Tower.zero) := host.isUniverse (Tower.IsUniverse.sort Tower.zero)
  have carrier : Typing R .nil (typeAt source.types 0 type) (sortTm Tower.zero) :=
    host_typed source proofName host (include_typed source proofName (typeAt_formed source type .nil))
  have shifted : Typing R (.snoc .nil (typeAt source.types 0 type)) (typeAt source.types 1 type)
      (sortTm Tower.zero) :=
    host_typed source proofName host (include_typed source proofName (typeAt_formed source type _))
  have newest : Typing R (.snoc .nil (typeAt source.types 0 type)) (.var 0)
      (typeAt source.types 1 type) := by
    simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
      (Typing.var (R := R) (Γ := .snoc .nil (typeAt source.types 0 type)) 0)
  have piFormed := pi_zero_at source proofName host carrier
    (.idForm shifted isSort newest newest)
  have lamTyped := Typing.lamIntro piFormed isSort (Typing.reflIntro newest)
  have codeTyped : Typing R .nil (reflexivityCode source type) (typeAt source.types 0 .prop) :=
    host_typed source proofName host (include_typed source proofName
      (represent_typed source (reflexivity type) (reflexivity_represented source type)))
  exact Typing.conv lamTyped (proof_formed_at source proofName host fresh codeTyped) isSort
    (.symm _ _ (stepStar_implies_conv decoded))

#print axioms computation
#print axioms decodes
#print axioms identityStep_preserves
#print axioms refl_realizes

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLIdentityEquality
