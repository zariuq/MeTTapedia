import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Confluence
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation

/-!
# Subject reduction for the certified-transform program

A *host* is a rules package that receives the linearized program and whose
conversion separates dependent functions and identity types.  In every host,
every equation of the program preserves every displayed type: both decoders of
the proof family, the equations of `add` and `pow`, and the fifteen package
equations.

* An equation whose arguments are pattern variables recovers its typed telescope
  from the declaration of its head.
* A constructor argument is inverted through the declaration of the
  constructor.
* Identity elimination at reflexivity uses the componentwise separation of
  identity types.  The reflexivity proof makes the point, the endpoint and
  the witness convertible, so the method's type converts to the result type.

The linearized program is a host, which gives contextual subject reduction
for it.  The conclusion is a judgment of the linearized program.  A judgment
of the draft's program is one of the linearized program, and every run of the
draft's program is a run of the linearized one.  Preservation of the draft's
own judgments needs a separate comparison of the two conversions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence Presentation.TelescopeAbstraction
open SetProfile (baseName constantName numTy zeroNative sucNative addNative
  holdsName targetRules)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence
open FormationSensitiveHOLGenericProofPreservation
open Mettapedia.Logic

/-- The proof family embeds in the linearized program. -/
theorem proofToLinear :
    (FormationSensitiveHOLGenericProofFamily.rules SetProfile.signature holdsName).Morphism
      linearRules (fun head => head) :=
  proofToPackage.comp packageToLinear

/-- Implication and the quantifiers of the profile are declared constants. -/
def connectives : DeclaredConnectives SetProfile.signature where
  implicationName := SetProfile.impName
  implication_eq := rfl
  implication_lookup := SetProfile.lookup_imp
  universalName := SetProfile.allName
  universal_eq := fun _ => rfl
  universal_lookup := SetProfile.lookup_allName

/-- The declared type of the iterator does not depend on its count. -/
theorem iterType_split :
    iterType =
      .pi numT (liftClosed (closeType iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0))))) :=
  rfl

/-- The declared telescope of `id:eliminate`: carrier, point, motive, method,
endpoint, path. -/
abbrev jDeclarationTelescope : Tower.Ctx 6 :=
  .snoc (.snoc jTelescope (.var 3)) (.id (.var 4) (.var 3) (.var 0))

theorem jType_close :
    jType = closeType jDeclarationTelescope (.app (.app (.var 3) (.var 1)) (.var 0)) :=
  jType_eq

/-! ## Hosts -/

/-- A rules package receiving the linearized program, whose conversion
separates dependent functions and identity types, and in which no identity
type converts to a universe head. -/
structure Host where
  rules : Rules Tower.Head
  embed : linearRules.Morphism rules (fun head => head)
  universes : UniverseRegularity rules
  piBoundary : PiConversionBoundary rules
  identityComponents : ∀ {n : Nat} {carrier carrier' left left' right right' : Tower.Tm n},
    Conv rules.headEq (.id carrier left right) (.id carrier' left' right') rules.computation →
      Conv rules.headEq carrier carrier' rules.computation ∧
        Conv rules.headEq left left' rules.computation ∧
          Conv rules.headEq right right' rules.computation
  identityNotHead : ∀ {n : Nat} {carrier left right : Tower.Tm n} {head : Tower.Head},
    ¬ Conv rules.headEq (.id carrier left right) (.head head) rules.computation

/-- A host whose computation is a definition by constructor patterns. -/
noncomputable def Host.ofConstructors (rules : Rules Tower.Head)
    (embed : linearRules.Morphism rules (fun head => head)) (universes : UniverseRegularity rules)
    (equations : Presentation.ConstructorSystem.ConstructorPresentation rules) : Host where
  rules := rules
  embed := embed
  universes := universes
  piBoundary := equations.piConversionBoundary
  identityComponents := equations.identity_components
  identityNotHead := equations.identity_not_head

namespace Host

variable (host : Host)

/-- The draft's program embeds in the host. -/
theorem fromPackage : packageRules.Morphism host.rules (fun head => head) :=
  packageToLinear.comp host.embed

/-- The proof family embeds in the host. -/
theorem fromProofFamily :
    (FormationSensitiveHOLGenericProofFamily.rules SetProfile.signature holdsName).Morphism
      host.rules (fun head => head) :=
  proofToLinear.comp host.embed

/-- Judgments of the draft's typing hold in the host. -/
theorem typed {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Typing R Γ term type) : Typing host.rules Γ term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typing.mapHead host.fromPackage

/-- A package declaration roots a declaration spine in the host. -/
theorem declaredSpine {name : DeclName} {type : Tower.Tm 0} {level : LevelExpr}
    (known : R.constantType name = some type) (formed : Typing R .nil type (sortTm level))
    {n : Nat} (Γ : Tower.Ctx n) :
    DeclarationSpine host.rules Γ (.const name) (liftClosed type) :=
  .constant (by simpa only [Tm.mapHead_id] using host.fromPackage.constantType known)
    (host.typed formed) (host.fromPackage.isUniverse (isUniverseAt level))

/-- A profile constant roots a declaration spine at its simple type. -/
theorem profileSpine {name : DeclName} {type : HOL.Ty SetProfile.SetBase}
    (known : SetProfile.signature.rules.constantType name =
      some (FormationSensitiveHOLInterface.typeAt SetProfile.signature.types 0 type))
    {n : Nat} (Γ : Tower.Ctx n) :
    DeclarationSpine host.rules Γ (.const name)
      (FormationSensitiveHOLInterface.typeAt SetProfile.signature.types n type) :=
  constantSpine SetProfile.signature holdsName host.fromProofFamily known Γ

theorem sucSpine {n : Nat} (Γ : Tower.Ctx n) :
    DeclarationSpine host.rules Γ (.const (constantName .suc))
      (FormationSensitiveHOLInterface.typeAt SetProfile.signature.types n
        (.arr numTy numTy)) :=
  host.profileSpine (SetProfile.lookup_constant .suc) Γ

/-! ### The decoders of the proof family -/

theorem implication_preserves {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
    (σ : Sub Tower.Head 2 n) {displayed : Tower.Tm n}
    (observed : Typing host.rules Γ (subst σ implicationLeft) displayed) :
    Typing host.rules Γ (subst σ implicationRight) displayed := by
  rw [implication_instance]
  exact decoder_preserves SetProfile.signature holdsName host.fromProofFamily
    SetProfile.holdsName_fresh connectives host.universes host.piBoundary formed observed
    (FormationSensitiveHOLGenericProofFamily.DecoderStep.implication (σ 1) (σ 0))

theorem universal_preserves {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
    (type : HOL.Ty SetProfile.SetBase) (σ : Sub Tower.Head 1 n) {displayed : Tower.Tm n}
    (observed : Typing host.rules Γ (subst σ (universalLeft type)) displayed) :
    Typing host.rules Γ (subst σ (universalRight type)) displayed := by
  rw [universal_instance]
  exact decoder_preserves SetProfile.signature holdsName host.fromProofFamily
    SetProfile.holdsName_fresh connectives host.universes host.piBoundary formed observed
    (FormationSensitiveHOLGenericProofFamily.DecoderStep.universal type (σ 0))

/-! ### The equations of `add` and `pow` -/

section Native

variable {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
  {displayed : Tower.Tm n}

include formed

theorem addZero_preserves (value : Tower.Tm n)
    (observed : Typing host.rules Γ (addNative value zeroNative) displayed) :
    Typing host.rules Γ value displayed := by
  obtain ⟨_, _, inner, _, _, _⟩ := observed.appGeneration
  obtain ⟨valueTyped, next, _⟩ := simpleArgument host.universes host.piBoundary formed
    (host.profileSpine (SetProfile.lookup_constant .add) Γ) inner
  obtain ⟨_, _, replay⟩ := simpleArgument host.universes host.piBoundary formed next observed
  exact replay valueTyped

theorem addSuc_preserves (left right : Tower.Tm n)
    (observed : Typing host.rules Γ (addNative left (sucNative right)) displayed) :
    Typing host.rules Γ (sucNative (addNative left right)) displayed := by
  obtain ⟨_, _, inner, _, _, _⟩ := observed.appGeneration
  have addition := host.profileSpine (SetProfile.lookup_constant .add) Γ
  obtain ⟨leftTyped, next, _⟩ :=
    simpleArgument host.universes host.piBoundary formed addition inner
  obtain ⟨successorTyped, _, replay⟩ :=
    simpleArgument host.universes host.piBoundary formed next observed
  obtain ⟨rightTyped, _, _⟩ :=
    simpleArgument host.universes host.piBoundary formed (host.sucSpine Γ) successorTyped
  exact replay (simpleApp (host.sucSpine Γ).typing
    (simpleApp (simpleApp addition.typing leftTyped) rightTyped))

theorem powZero_preserves (base : Tower.Tm n)
    (observed : Typing host.rules Γ
      (.app (.app (.const (constantName .pow)) zeroNative) base) displayed) :
    Typing host.rules Γ base displayed := by
  obtain ⟨_, _, inner, _, _, _⟩ := observed.appGeneration
  obtain ⟨_, next, _⟩ := simpleArgument host.universes host.piBoundary formed
    (host.profileSpine (SetProfile.lookup_constant .pow) Γ) inner
  obtain ⟨baseTyped, _, replay⟩ :=
    simpleArgument host.universes host.piBoundary formed next observed
  exact replay baseTyped

theorem powSuc_preserves (count base : Tower.Tm n)
    (observed : Typing host.rules Γ
      (.app (.app (.const (constantName .pow)) (sucNative count)) base) displayed) :
    Typing host.rules Γ
      (.app (.const (constantName .power)) (.app (.app (.const (constantName .pow)) count) base))
      displayed := by
  obtain ⟨_, _, inner, _, _, _⟩ := observed.appGeneration
  have power := host.profileSpine (SetProfile.lookup_constant .pow) Γ
  obtain ⟨successorTyped, next, _⟩ :=
    simpleArgument host.universes host.piBoundary formed power inner
  obtain ⟨baseTyped, _, replay⟩ :=
    simpleArgument host.universes host.piBoundary formed next observed
  obtain ⟨countTyped, _, _⟩ :=
    simpleArgument host.universes host.piBoundary formed (host.sucSpine Γ) successorTyped
  exact replay (simpleApp (host.profileSpine (SetProfile.lookup_constant .power) Γ).typing
    (simpleApp (simpleApp power.typing countTyped) baseTyped))

end Native

/-! ### Equations over pattern variables -/

/-- An equation that applies a declared constant to its pattern variables
preserves typing when its right side is typed at the declared result in the
declared telescope. -/
theorem variableEquation_preserves {k : Nat} (telescope : Tower.Ctx k) (result right : Tower.Tm k)
    {name : DeclName} {level : LevelExpr}
    (known : R.constantType name = some (closeType telescope result))
    (formedType : Typing R .nil (closeType telescope result) (sortTm level))
    (rightTyped : Typing R telescope right result)
    {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
    (σ : Sub Tower.Head k n) {displayed : Tower.Tm n}
    (observed : Typing host.rules Γ (applyClosed telescope σ (.const name)) displayed) :
    Typing host.rules Γ (subst σ right) displayed := by
  obtain ⟨morphism, _, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed telescope result σ (host.declaredSpine known formedType Γ) observed
  exact replay ((host.typed rightTyped).substitute morphism)

/-! ### Constructor arguments -/

/-- The head of an application spine is typed. -/
theorem applyClosed_head {n k : Nat} {Γ : Tower.Ctx n} (telescope : Tower.Ctx k) :
    ∀ (σ : Sub Tower.Head k n) {function displayed : Tower.Tm n},
      Typing host.rules Γ (applyClosed telescope σ function) displayed →
        ∃ type, Typing host.rules Γ function type := by
  induction telescope with
  | nil => intro σ function displayed typing; exact ⟨_, typing⟩
  | snoc prior _ ih =>
      intro σ function displayed typing
      obtain ⟨_, _, functionTyped, _, _, _⟩ := typing.appGeneration
      exact ih _ functionTyped

/-- The iterator applied to a typed count roots the spine of its remaining
telescope. -/
theorem iterSpine {n : Nat} {Γ : Tower.Ctx n} {count : Tower.Tm n}
    (countTyped : Typing host.rules Γ count numT) :
    DeclarationSpine host.rules Γ (.app (.const iterName) count)
      (liftClosed (closeType iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0))))) := by
  have spine := host.declaredSpine lookup_iter iterType_formed Γ
  rw [iterType_split] at spine
  simpa only [inst0, rename_liftClosed, subst_liftClosed] using spine.app countTyped

section Constructors

variable {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
  {displayed : Tower.Tm n}

include formed

/-- `num-rec P z s zero = z`. -/
theorem numRecZero_preserves (σ : Sub Tower.Head 3 n)
    (observed : Typing host.rules Γ (subst σ (numRecApp (.var 2) (.var 1) (.var 0) zeroNative))
      displayed) :
    Typing host.rules Γ (σ 1) displayed := by
  obtain ⟨morphism, _, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed (.snoc numRecTelescope numT) (.app (.var 3) (.var 0))
    (consSub zeroNative σ) (host.declaredSpine lookup_numRec numRecType_formed Γ) observed
  have typed : FormationSensitive.CtxMor host.rules numRecTelescope Γ σ := morphism.dropNewest
  exact replay ((host.typed numRecZeroTyped.right_typed).substitute typed)

/-- `num-rec P z s (suc v) = s v (num-rec P z s v)`. -/
theorem numRecSuc_preserves (σ : Sub Tower.Head 4 n)
    (observed : Typing host.rules Γ
      (subst σ (numRecApp (.var 3) (.var 2) (.var 1) (sucNative (.var 0)))) displayed) :
    Typing host.rules Γ
      (subst σ (app2 (.var 1) (.var 0) (numRecApp (.var 3) (.var 2) (.var 1) (.var 0))))
      displayed := by
  obtain ⟨morphism, _, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed (.snoc numRecTelescope numT) (.app (.var 3) (.var 0))
    (consSub (sucNative (σ 0)) (fun index => σ index.succ))
    (host.declaredSpine lookup_numRec numRecType_formed Γ) observed
  have successorTyped : Typing host.rules Γ (sucNative (σ 0)) numT := morphism 0
  obtain ⟨predecessorTyped, _, _⟩ :=
    simpleArgument host.universes host.piBoundary formed (host.sucSpine Γ) successorTyped
  have tail : FormationSensitive.CtxMor host.rules numRecTelescope Γ
      (fun index => σ index.succ) :=
    morphism.dropNewest
  have typed := tail.extend (type := numT) predecessorTyped
  rw [consSub_eta σ] at typed
  exact replay ((host.typed numRecSucTyped.right_typed).substitute typed)

/-- `iterCert zero A P step x e = (x, e)`. -/
theorem iterZero_preserves (σ : Sub Tower.Head 5 n)
    (observed : Typing host.rules Γ
      (subst σ (iterApp zeroNative (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))) displayed) :
    Typing host.rules Γ (subst σ (.pair (.var 1) (.var 0))) displayed := by
  obtain ⟨morphism, _, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0))) σ
    (host.iterSpine (host.typed zeroNative_typed)) observed
  exact replay ((host.typed iterZeroTyped.right_typed).substitute morphism)

/-- `iterCert (suc k) A P step x e = step x e`, shared with the rest of the
iteration. -/
theorem iterSuc_preserves (σ : Sub Tower.Head 6 n)
    (observed : Typing host.rules Γ
      (subst σ (iterApp (sucNative (.var 5)) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)))
      displayed) :
    Typing host.rules Γ
      (subst σ (CertifiedTransforms.shared (.var 2) (iterPartial (.var 5) (.var 4) (.var 3) (.var 2))
        (.var 1) (.var 0))) displayed := by
  have call : Typing host.rules Γ
      (applyClosed iterTelescope (fun index => σ index.castSucc)
        (.app (.const iterName) (sucNative (σ 5)))) displayed := observed
  obtain ⟨_, headTyped⟩ := host.applyClosed_head iterTelescope _ call
  have spine := host.declaredSpine lookup_iter iterType_formed Γ
  rw [iterType_split] at spine
  obtain ⟨countTyped, _, _, _⟩ :=
    spine.recoverApplication host.universes host.piBoundary formed headTyped
  have successorTyped : Typing host.rules Γ (sucNative (σ 5)) numT := countTyped
  obtain ⟨predecessorTyped, _, _⟩ :=
    simpleArgument host.universes host.piBoundary formed (host.sucSpine Γ) successorTyped
  obtain ⟨morphism, _, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed iterTelescope (.sigma (.var 4) (.app (.var 4) (.var 0)))
    (fun index => σ index.castSucc) (host.iterSpine successorTyped) call
  have typed : FormationSensitive.CtxMor host.rules iterSucTelescope Γ σ := by
    intro index
    refine Fin.cases ?_ (fun index => ?_) index
    · exact morphism 0
    refine Fin.cases ?_ (fun index => ?_) index
    · exact morphism 1
    refine Fin.cases ?_ (fun index => ?_) index
    · exact morphism 2
    refine Fin.cases ?_ (fun index => ?_) index
    · exact morphism 3
    refine Fin.cases ?_ (fun index => ?_) index
    · exact morphism 4
    refine Fin.cases ?_ (fun index => index.elim0) index
    exact predecessorTyped
  exact replay ((host.typed iterSucTyped.right_typed).substitute typed)

end Constructors

/-! ### Identity elimination at reflexivity -/

/-- A reflexivity proof of `Id A x y` makes the witness, the point and the
endpoint convertible. -/
theorem refl_endpoints {n : Nat} {Γ : Tower.Ctx n} {witness carrier point endpoint : Tower.Tm n}
    (typing : Typing host.rules Γ (.refl witness) (.id carrier point endpoint)) :
    Conv host.rules.headEq witness point host.rules.computation ∧
      Conv host.rules.headEq witness endpoint host.rules.computation := by
  obtain ⟨_, _, adjustment⟩ := CertifiedTransforms.reflGeneration typing
  have conversion := adjustment.toConvOfTargetDisjointHeads
    (fun _ conversion => host.identityNotHead conversion)
  obtain ⟨_, toPoint, toEndpoint⟩ := host.identityComponents conversion
  exact ⟨toPoint, toEndpoint⟩

/-- `id:eliminate A x P d y (refl z) = d`, at every type the redex has. -/
theorem jLinear_preserves {n : Nat} {Γ : Tower.Ctx n} (formed : ContextFormation host.rules Γ)
    (σ : Sub Tower.Head 6 n) {displayed : Tower.Tm n}
    (observed : Typing host.rules Γ
      (subst σ (jApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.refl (.var 0)))) displayed) :
    Typing host.rules Γ (σ 2) displayed := by
  have spine := host.declaredSpine lookup_j jType_formed Γ
  rw [jType_close] at spine
  obtain ⟨morphism, application, _, replay⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed jDeclarationTelescope (.app (.app (.var 3) (.var 1)) (.var 0))
    (consSub (.refl (σ 0)) (fun index => σ index.succ)) spine observed
  have methodTyped : Typing host.rules Γ (σ 2) (.app (.app (σ 3) (σ 4)) (.refl (σ 4))) :=
    morphism 2
  have pathTyped : Typing host.rules Γ (.refl (σ 0)) (.id (σ 5) (σ 4) (σ 1)) := morphism 0
  obtain ⟨toPoint, toEndpoint⟩ := host.refl_endpoints pathTyped
  have endpoints : Conv host.rules.headEq (σ 4) (σ 1) host.rules.computation :=
    .trans _ _ _ (.symm _ _ toPoint) toEndpoint
  have reflexivity : Conv host.rules.headEq (.refl (σ 4)) (.refl (σ 0)) host.rules.computation :=
    Conv.mapCompatible Tm.refl (fun step => .congRefl step) (.symm _ _ toPoint)
  have motive : Conv host.rules.headEq (.app (.app (σ 3) (σ 4)) (.refl (σ 4)))
      (.app (.app (σ 3) (σ 1)) (.refl (σ 0))) host.rules.computation :=
    Conv.congApp (Conv.congApp (.refl _) endpoints) reflexivity
  obtain ⟨_, universeResult, resultFormed⟩ := application.typing.regularity host.universes formed
  exact replay (.conv methodTyped resultFormed universeResult motive)

/-! ### Every equation of the linearized program -/

/-- Every equation of the linearized program preserves every displayed type in
the host. -/
theorem linearSchema_preserves {arity n : Nat} {left right : Tower.Tm arity}
    (rule : LinearSchema left right) (σ : Sub Tower.Head arity n)
    {Γ : Tower.Ctx n} {displayed : Tower.Tm n} (formed : ContextFormation host.rules Γ)
    (observed : Typing host.rules Γ (subst σ left) displayed) :
    Typing host.rules Γ (subst σ right) displayed := by
  cases rule with
  | implication => exact host.implication_preserves formed σ observed
  | universal type => exact host.universal_preserves formed type σ observed
  | native listed =>
      simp only [SetProfile.nativeEquations, List.mem_cons, List.not_mem_nil,
        or_false] at listed
      rcases listed with same | same | same | same <;> cases same
      · exact host.addZero_preserves formed (σ 0) observed
      · exact host.addSuc_preserves formed (σ 1) (σ 0) observed
      · exact host.powZero_preserves formed (σ 0) observed
      · exact host.powSuc_preserves formed (σ 1) (σ 0) observed
  | package listed =>
      simp only [linearEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with same | same | same | same | same | same | same | same | same | same |
        same | same | same | same | same <;> cases same
      · exact host.jLinear_preserves formed σ observed
      · exact host.numRecZero_preserves formed σ observed
      · exact host.numRecSuc_preserves formed σ observed
      · exact host.variableEquation_preserves eqAtTyped.telescope eqAtTyped.type _ lookup_eqAt
          eqAtType_formed eqAtTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves sucMoveTyped.telescope sucMoveTyped.type _
          lookup_sucMove sucMoveType_formed sucMoveTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves keepTyped.telescope keepTyped.type _ lookup_keep
          keepType_formed keepTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves transportTyped.telescope transportTyped.type _
          lookup_transport transportType_formed transportTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves composeTyped.telescope composeTyped.type _
          lookup_compose composeType_formed composeTyped.right_typed formed σ observed
      · exact host.iterZero_preserves formed σ observed
      · exact host.iterSuc_preserves formed σ observed
      · exact host.variableEquation_preserves returnIterTyped.telescope returnIterTyped.type _
          lookup_returnIter returnIterType_formed returnIterTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves sucStepTyped.telescope sucStepTyped.type _
          lookup_sucStep sucStepType_formed sucStepTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves holdsAtTyped.telescope holdsAtTyped.type _
          lookup_holdsAt holdsAtType_formed holdsAtTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves holdsMoveTyped.telescope holdsMoveTyped.type _
          lookup_holdsMove holdsMoveType_formed holdsMoveTyped.right_typed formed σ observed
      · exact host.variableEquation_preserves holdsStepTyped.telescope holdsStepTyped.type _
          lookup_holdsStep holdsStepType_formed holdsStepTyped.right_typed formed σ observed

end Host

/-! ## The linearized program -/

theorem universes : UniverseRegularity linearRules :=
  (((towerUniverseRegularity.includeSignature SetProfile.declarations).includeSignature
      (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.signature
        holdsName)).includeSignature SetProfile.assumptionDeclarations).includeSignature
    linearDeclarations

theorem heads : HeadPreservation linearRules :=
  HeadPreservation.includeSignature
    (HeadPreservation.includeSignature
      (HeadPreservation.includeSignature
        (HeadPreservation.includeSignature towerHeadPreservation SetProfile.declarations)
        (FormationSensitiveHOLGenericProofFamily.declarations SetProfile.signature
          holdsName))
      SetProfile.assumptionDeclarations)
    linearDeclarations

/-- The linearized program is a host of itself. -/
noncomputable def linearHost : Host :=
  Host.ofConstructors linearRules (Rules.Morphism.identity linearRules) universes linearConstructors

theorem rootPreservation : RootPreservation linearRules := by
  intro n Γ source target displayed formed observed step
  obtain ⟨_, _, _, σ, rule, rfl, rfl⟩ := linearSchema_cover step
  exact linearHost.linearSchema_preserves rule σ formed observed

/-- Contextual subject reduction, including computation under binders, in
dependent arguments and in identity endpoints. -/
theorem step_preserves {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment linearRules Γ source displayed)
    (step : Step linearRules.headEq source target linearRules.computation) :
    Judgment linearRules Γ target displayed :=
  judgment.step_preserves universes piConversionBoundary sigmaConversionBoundary heads
    rootPreservation step

theorem steps_preserve {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment linearRules Γ source displayed)
    (steps : StepStar linearRules source target) :
    Judgment linearRules Γ target displayed :=
  judgment.steps_preserve universes piConversionBoundary sigmaConversionBoundary heads
    rootPreservation steps

/-! ## The evaluator's runs -/

/-- Every run of the draft's program is a run of the linearized program. -/
theorem runs_linear {n : Nat} {source target : Tower.Tm n}
    (runs : CertifiedTransformProgram.Execution.Runs source target) :
    StepStar linearRules source target := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih =>
      refine .tail ih ?_
      simpa only [Tm.mapHead_id] using
        StepCore.mapHead (fun head => head) packageToLinear.headEq packageToLinear.computation step

/-- Judgments of the draft's program are judgments of the linearized program. -/
theorem judgment_linear {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : Judgment R Γ term type) : Judgment linearRules Γ term type :=
  ⟨by simpa only [Ctx.mapHead_id] using judgment.context.mapHead packageToLinear,
    linearHost.typed judgment.typing⟩

/-- Evaluation is typing reduction: every run of the evaluator keeps the type
of the judgment it starts from, as a judgment of the linearized program. -/
theorem runs_preserve {n : Nat} {Γ : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : Judgment R Γ source displayed)
    (runs : CertifiedTransformProgram.Execution.Runs source target) :
    Judgment linearRules Γ target displayed :=
  steps_preserve (judgment_linear judgment) (runs_linear runs)

/-- Identity elimination returns its method once the path computes to
reflexivity.  The kernel fires it only then, after also comparing the point,
the endpoint and the witness, so each firing is a run of the linearized
program. -/
theorem identityElimination_runs {n : Nat}
    {carrier point motive method endpoint path witness : Tower.Tm n}
    (pathRuns : StepStar linearRules path (.refl witness)) :
    StepStar linearRules (jApp carrier point motive method endpoint path) method := by
  have congruence : ∀ {target : Tower.Tm n}, StepStar linearRules path target →
      StepStar linearRules (jApp carrier point motive method endpoint path)
        (jApp carrier point motive method endpoint target) := by
    intro target runs
    induction runs with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih (.congAppArg step)
  exact .tail (congruence pathRuns) (.root (linearSchema_sound
    (.package (List.getElem_mem (l := linearEquations) (n := 0) (by decide)))
    (CertifiedTransformProgram.Execution.patternValues
      ![carrier, point, motive, method, endpoint, witness])))

/-- Every run of the closed consumer call ends in a pair typed at
`Σ k : num. holdsAt k`, not only the computed one. -/
theorem holds_consumer_runs_typed (count : Nat) {target : Tower.Tm 0}
    (runs : CertifiedTransformProgram.Execution.Runs
      (iterApp (CertifiedTransformProgram.Execution.numeral count) numT (.const holdsAtName)
        (.const holdsStepName) zeroNative CertifiedTransformProgram.Execution.holdsBase) target) :
    Judgment linearRules .nil target (.sigma numT (holdsAtApp (.var 0))) :=
  runs_preserve ⟨.nil, (CertifiedTransformProgram.Execution.holds_consumer_typed count).1⟩ runs

/-- The same at an open count: every run of the call at the index `k : num`
keeps the consumer's type. -/
theorem holds_open_count_runs_typed {target : Tower.Tm 1}
    (runs : CertifiedTransformProgram.Execution.Runs
      (iterApp (.var 0) numT (.const holdsAtName) (.const holdsStepName) zeroNative
        CertifiedTransformProgram.Execution.holdsBase) target) :
    Judgment linearRules (.snoc .nil numT) target (.sigma numT (holdsAtApp (.var 0))) :=
  runs_preserve ⟨.snoc .nil numT_typed (isUniverseAt Tower.zero),
    CertifiedTransformProgram.Execution.holds_open_count⟩ runs

/-! ## Axiom audit -/

#print axioms connectives
#print axioms universes
#print axioms heads
#print axioms Host.addSuc_preserves
#print axioms Host.powSuc_preserves
#print axioms Host.variableEquation_preserves
#print axioms Host.numRecSuc_preserves
#print axioms Host.iterSuc_preserves
#print axioms Host.jLinear_preserves
#print axioms Host.linearSchema_preserves
#print axioms rootPreservation
#print axioms step_preserves
#print axioms steps_preserve
#print axioms runs_linear
#print axioms runs_preserve
#print axioms identityElimination_runs
#print axioms holds_consumer_runs_typed
#print axioms holds_open_count_runs_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation
