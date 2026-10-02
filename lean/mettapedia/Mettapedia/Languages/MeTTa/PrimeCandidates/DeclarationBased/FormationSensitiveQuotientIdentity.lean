import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientCwfControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientUniverses
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveBasedIdentity
import Mettapedia.TypeTheory.ContextualBasedIdentityOperations

/-!
# Native identity in the formed conversion-class CwF

Identity formation and reflexivity descend from their actual refined native
constructors, independently of a chosen formation-level witness. The fixed
native J declaration has a more specific scope: its element universe is
parameter zero and its motive universe is parameter one. Its admitted
telescope, rather than every type and motive of the CwF, licenses elimination.

All equalities below use the existing authored conversion quotient. No native
K/UIP, extra conversion rule, level instantiation of a fixed declaration, or
interpretation in an independent semantic host is asserted.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientIdentity

open _root_.CategoryTheory FormationSensitive
open Mettapedia.TypeTheory.ContextualTypeOperations
open QuotientCwf

variable {Head : Type} {rules : Rules Head}

def nativeId {context : Context rules} (type : TypeOver context)
    (left right : Term context type) : TypeOver context where
  code := .id type.code left.code right.code
  level := type.level
  universeWitness := type.universeWitness
  formed := .idForm type.formed type.universeWitness left.typed right.typed

def nativeRefl {context : Context rules} {type : TypeOver context}
    (term : Term context type) : Term context (nativeId type term term) :=
  ⟨.refl term.code, .reflIntro term.typed⟩

noncomputable def selectedTerm {context : QContext rules} {type : Ty context}
    (term : QuotientCwf.Tm context type) : Term context.as (typeRepresentative type) :=
  termRepresentative (typeRepresentative type) term.val
    (term.property.trans (typeRepresentative_class type).symm)

theorem selectedTerm_class {context : QContext rules} {type : Ty context}
    (term : QuotientCwf.Tm context type) : QTerm.mk (selectedTerm term) = term.val :=
  termRepresentative_class _ _ _

noncomputable def idTy {context : QContext rules} (type : Ty context)
    (left right : QuotientCwf.Tm context type) : Ty context :=
  QType.mk (nativeId (typeRepresentative type) (selectedTerm left) (selectedTerm right))

/-- Any independently supplied native representatives compute the same
identity type class. The proof uses three native constructor congruences,
not equality of raw annotations or their universe witnesses. -/
theorem idTy_eq_native {context : QContext rules} {type : Ty context}
    (left right : QuotientCwf.Tm context type) (actual : TypeOver context.as)
    (actualLeft actualRight : Term context.as actual)
    (typeClass : QType.mk actual = type)
    (leftClass : QTerm.mk actualLeft = left.val)
    (rightClass : QTerm.mk actualRight = right.val) :
    idTy type left right = QType.mk (nativeId actual actualLeft actualRight) := by
  apply (QType.mk_eq_iff _ _).mpr
  exact Conv.congId
    ((QType.mk_eq_iff _ _).mp ((typeRepresentative_class type).trans typeClass.symm))
    ((QTerm.mk_eq_iff _ _).mp ((selectedTerm_class left).trans leftClass.symm)).2
    ((QTerm.mk_eq_iff _ _).mp ((selectedTerm_class right).trans rightClass.symm)).2

theorem idTy_mk {context : Context rules} (type : TypeOver context)
    (left right : Term context type) :
    idTy (context := (quotientProjection rules).obj context) (QType.mk type)
      (TermFibre.mk left) (TermFibre.mk right) = QType.mk (nativeId type left right) :=
  idTy_eq_native _ _ type left right rfl rfl rfl

theorem idTy_substitution {source target : QContext rules}
    (substitution : source ⟶ target) (type : Ty target)
    (left right : QuotientCwf.Tm target type) :
    tySub (idTy type left right) substitution =
      idTy (tySub type substitution) (tmSub left substitution) (tmSub right substitution) := by
  induction substitution using Quot.inductionOn with
  | h raw =>
    symm
    exact idTy_eq_native _ _ ((typeRepresentative type).reindex raw)
      ((selectedTerm left).reindex raw) ((selectedTerm right).reindex raw)
      (congrArg (fun next => next.reindex raw) (typeRepresentative_class type))
      (congrArg (fun next => next.reindex raw) (selectedTerm_class left))
      (congrArg (fun next => next.reindex raw) (selectedTerm_class right))

noncomputable def formation (rules : Rules Head) :
    IdentityFormationOperations (QuotientCwf.cwf rules) where
  idTy := idTy

theorem formation_substitution (rules : Rules Head) :
    StrictIdentityFormationSubstitution (formation rules) := idTy_substitution

noncomputable def refl {context : QContext rules} {type : Ty context}
    (term : QuotientCwf.Tm context type) : QuotientCwf.Tm context (idTy type term term) :=
  ⟨QTerm.mk (nativeRefl (selectedTerm term)), rfl⟩

theorem refl_eq_native {context : QContext rules} {type : Ty context}
    (term : QuotientCwf.Tm context type) (actual : TypeOver context.as)
    (actualTerm : Term context.as actual)
    (typeClass : QType.mk actual = type)
    (termClass : QTerm.mk actualTerm = term.val) :
    (refl term).val = QTerm.mk (nativeRefl actualTerm) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨(QType.mk_eq_iff _ _).mp
    (idTy_eq_native term term actual actualTerm actualTerm typeClass termClass termClass), ?_⟩
  exact Conv.mapCompatible Presentation.Tm.refl (fun step => .congRefl step)
    ((QTerm.mk_eq_iff _ _).mp ((selectedTerm_class term).trans termClass.symm)).2

theorem refl_substitution_value {source target : QContext rules}
    (substitution : source ⟶ target) {type : Ty target}
    (term : QuotientCwf.Tm target type) :
    (tmSub (refl term) substitution).val = (refl (tmSub term substitution)).val := by
  induction substitution using Quot.inductionOn with
  | h raw =>
    symm
    exact refl_eq_native _ ((typeRepresentative type).reindex raw)
      ((selectedTerm term).reindex raw)
      (congrArg (fun next => next.reindex raw) (typeRepresentative_class type))
      (congrArg (fun next => next.reindex raw) (selectedTerm_class term))

noncomputable def reflexivity (rules : Rules Head) :
    IdentityReflexivityOperations (formation rules) where
  refl := refl

theorem reflexivity_substitution (rules : Rules Head) :
    StrictReflexivitySubstitution (reflexivity rules) := by
  intro source target substitution type term
  have sameType := idTy_substitution substitution type term term
  have sameValue := refl_substitution_value substitution term
  change HEq (tmSub (refl term) substitution) (refl (tmSub term substitution))
  exact (Subtype.heq_iff_coe_eq (fun _ => by rw [sameType])).mpr sameValue

/-! ## Comparison with the chosen CwF based context -/

def nativeWitness {context : Context rules} (type : TypeOver context)
    (left : Term context type) : TypeOver (extend context type) :=
  nativeId (type.reindex (projectionHom context type))
    (left.reindex (projectionHom context type)) (newest context type)

private def doubleExtensionHom {context : Context rules}
    (first second : TypeOver context)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (baseConversion : Conv rules.headEq first.code second.code rules.computation)
    (bodyConversion : Conv rules.headEq firstBody.code secondBody.code rules.computation) :
    extend (extend context first) firstBody ⟶ extend (extend context second) secondBody where
  substitution := ids
  typed := by
    have base := (extensionComparison first second baseConversion).hom.typed
    have secondFormed : Typing rules (extend context first).raw secondBody.code (.head secondBody.level) := by
      simpa only [extensionComparison_hom_substitution, subst_ids, subst] using
        secondBody.formed.substitute base
    intro index
    rw [subst_ids]
    refine Fin.cases ?_ (fun prior => ?_) index
    · exact .conv (.var 0) secondFormed.weaken secondBody.universeWitness
        (bodyConversion.renameTerms wk)
    · simpa only [extensionComparison_hom_substitution, subst_ids, ids, rename,
        Ctx.lookup_snoc_succ, extend, Presentation.wk] using
        (base prior).weaken (extension := firstBody.code)

/-- Two independently formed dependent annotations yield an isomorphism,
not equality of the raw context objects. Both directions are actual typed
identity substitutions through both binders. -/
def doubleExtensionComparison {context : Context rules}
    (first second : TypeOver context)
    (firstBody : TypeOver (extend context first)) (secondBody : TypeOver (extend context second))
    (baseConversion : Conv rules.headEq first.code second.code rules.computation)
    (bodyConversion : Conv rules.headEq firstBody.code secondBody.code rules.computation) :
    extend (extend context first) firstBody ≅ extend (extend context second) secondBody where
  hom := doubleExtensionHom first second firstBody secondBody baseConversion bodyConversion
  inv := doubleExtensionHom second first secondBody firstBody baseConversion.symm bodyConversion.symm
  hom_inv_id := Hom.ext (subComp_ids_left ids)
  inv_hom_id := Hom.ext (subComp_ids_left ids)

noncomputable def chosenWitness {context : Context rules} (type : TypeOver context)
    (left : Term context type) : TypeOver (extend context (typeRepresentative (QType.mk type))) :=
  typeRepresentative
    (Mettapedia.TypeTheory.ContextualBasedIdentityOperations.witnessType (formation rules)
      (context := (quotientProjection rules).obj context) (TermFibre.mk left))

theorem chosenWitness_conversion {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    Conv rules.headEq (chosenWitness type left).code (nativeWitness type left).code rules.computation := by
  let chosen := typeRepresentative (QType.mk type)
  let point := selectedTerm (context := (quotientProjection rules).obj context) (TermFibre.mk left)
  have typeConversion : Conv rules.headEq chosen.code type.code rules.computation :=
    (QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type))
  have pointConversion : Conv rules.headEq point.code left.code rules.computation :=
    ((QTerm.mk_eq_iff _ _).mp (selectedTerm_class
      (context := (quotientProjection rules).obj context) (TermFibre.mk left))).2
  have witness := idTy_eq_native
    (tmSub (target := (quotientProjection rules).obj context) (TermFibre.mk left)
      (QuotientCwf.wk (QType.mk type)))
    (QuotientCwf.vz (QType.mk type))
    (chosen.reindex (projectionHom context chosen))
    (point.reindex (projectionHom context chosen)) (newest context chosen)
    (congrArg (fun next => next.reindex (projectionHom context chosen))
      (typeRepresentative_class (QType.mk type)))
    (congrArg (fun next => next.reindex (projectionHom context chosen))
      (selectedTerm_class (context := (quotientProjection rules).obj context) (TermFibre.mk left))) rfl
  have first : Conv rules.headEq (chosenWitness type left).code
      (nativeWitness chosen point).code rules.computation :=
    (QType.mk_eq_iff _ _).mp ((typeRepresentative_class _).trans witness)
  apply first.trans
  change Conv rules.headEq
    (.id (subst projection chosen.code) (subst projection point.code) (.var 0))
    (.id (subst projection type.code) (subst projection left.code) (.var 0)) rules.computation
  exact Conv.congId (typeConversion.substitute projection)
    (pointConversion.substitute projection) (.refl _)

/-- The raw native endpoint/path context presents the actual based context
of the constructed CwF. Its comparison does not require selected raw
annotations to be equal. -/
noncomputable def chosenBasedContext {context : Context rules} (type : TypeOver context)
    (left : Term context type) : QContext rules :=
  (quotientProjection rules).obj
    (extend (extend context (typeRepresentative (QType.mk type))) (chosenWitness type left))

theorem chosenBasedContext_eq_based {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    chosenBasedContext type left =
      Mettapedia.TypeTheory.ContextualBasedIdentityOperations.basedContext (formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left) := rfl

noncomputable def basedPresentation {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    _root_.CategoryTheory.Iso (C := QContext rules)
      (chosenBasedContext type left)
      ((quotientProjection rules).obj (extend (extend context type) (nativeWitness type left))) :=
  (quotientProjection rules).mapIso
    (doubleExtensionComparison (typeRepresentative (QType.mk type)) type
      (chosenWitness type left) (nativeWitness type left)
      ((QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type)))
      (chosenWitness_conversion type left))

/-! ## The exact admitted scope of the native based eliminator -/

namespace Based

open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic

variable {signature : Declaration.Signature Tower.Head}

/-- Inputs carry the actual declaration-telescope substitution, not a proof
of the desired J result. The ambient context is independently formed. -/
structure Admitted (context : Context (OpaqueRelatorExtension.rules signature)) where
  type : Tower.Tm context.arity
  left : Tower.Tm context.arity
  motive : Tower.Tm context.arity
  method : Tower.Tm context.arity
  typed : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
    contextAXPD context.raw (identitySchemaSubstitution type left motive method)

namespace Admitted

variable {context : Context (OpaqueRelatorExtension.rules signature)}

theorem parameters (input : Admitted context) :
    FormationSensitiveBasedIdentity.Parameters signature context.raw
      input.type input.left input.motive input.method := ⟨context.formed, input.typed⟩

def element (input : Admitted context) : TypeOver context where
  code := input.type
  level := .sort elementLevel
  universeWitness := .sort elementLevel
  formed := FormationSensitiveBasedIdentity.parameters_type input.parameters

def leftTerm (input : Admitted context) : Term context input.element :=
  ⟨input.left, FormationSensitiveBasedIdentity.parameters_left input.parameters⟩

def basedContext (input : Admitted context) :
    Context (OpaqueRelatorExtension.rules signature) where
  arity := context.arity + 2
  raw := FormationSensitiveBasedIdentity.basedContext context.raw input.type input.left
  formed := FormationSensitiveBasedIdentity.basedContext_formed input.parameters

private theorem schema_motive_formed :
    Typing IntrinsicRelator.rules contextAXPDYQ
      (.app (.app (.var 3) (.var 1)) (.var 0)) (sortTm motiveLevel) := by
  have first : Typing IntrinsicRelator.rules contextAXPDYQ
      (.app (.var 3) (.var 1))
      (.pi (.id (.var 5) (.var 4) (.var 1)) (sortTm motiveLevel)) := by
    have result := Typing.appElim (R := IntrinsicRelator.rules)
      (Typing.var (Γ := contextAXPDYQ) 3) (Typing.var (Γ := contextAXPDYQ) 1)
    convert result using 1
    decide
  simpa only [sortTm, inst0, subst] using Typing.appElim first (Typing.var 0)

def motiveType (input : Admitted context) : TypeOver input.basedContext where
  code := FormationSensitiveBasedIdentity.motiveBody input.motive
  level := .sort motiveLevel
  universeWitness := .sort motiveLevel
  formed := (OpaqueRelatorExtension.relator_typing schema_motive_formed).substitute
    ((input.typed.lift (.var 3)).lift (.id (.var 4) (.var 3) (.var 0)))

def methodType (input : Admitted context) : TypeOver context where
  code := FormationSensitiveBasedIdentity.methodType input.left input.motive
  level := .sort motiveLevel
  universeWitness := .sort motiveLevel
  formed := (OpaqueRelatorExtension.relator_typing
    FormationSensitiveNativeIdentity.identityReflCaseType_hasType).weaken.substitute input.typed

def nativeJ (input : Admitted context) : Term input.basedContext input.motiveType :=
  ⟨FormationSensitiveBasedIdentity.genericTerm input.type input.left input.motive input.method,
    (FormationSensitiveBasedIdentity.generic_judgment input.parameters).typing⟩

def nativeMethod (input : Admitted context) : Term context input.methodType :=
  ⟨input.method, (FormationSensitiveBasedIdentity.method_judgment input.parameters).typing⟩

def j (input : Admitted context) :
    (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)).Tm
      ((quotientProjection _).obj input.basedContext) (QType.mk input.motiveType) :=
  TermFibre.mk input.nativeJ

def base (input : Admitted context) :
    (QuotientCwf.cwf (OpaqueRelatorExtension.rules signature)).Tm
      ((quotientProjection _).obj context) (QType.mk input.methodType) :=
  TermFibre.mk input.nativeMethod

def reflSection (input : Admitted context) : context ⟶ input.basedContext :=
  ⟨FormationSensitiveBasedIdentity.reflexivitySub input.left,
    FormationSensitiveBasedIdentity.reflexivitySub_typed input.parameters⟩

theorem motive_reflexivity (input : Admitted context) :
    tySub (QType.mk input.motiveType) (project input.reflSection) =
      QType.mk input.methodType := by
  apply (QType.mk_eq_iff _ _).mpr
  change Conv _ (subst (FormationSensitiveBasedIdentity.reflexivitySub input.left)
    (FormationSensitiveBasedIdentity.motiveBody input.motive)) _ _
  rw [FormationSensitiveBasedIdentity.reflexivitySub_motiveBody]
  exact .refl _

/-- The actual declared iota root becomes the beta equality in the same
constructed term fibre. Both annotations are independently formed. -/
theorem beta_value (input : Admitted context) :
    (tmSub input.j (project input.reflSection)).val = input.base.val := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨(QType.mk_eq_iff _ _).mp input.motive_reflexivity, ?_⟩
  change Conv _ (subst (FormationSensitiveBasedIdentity.reflexivitySub input.left)
    (FormationSensitiveBasedIdentity.genericTerm input.type input.left input.motive input.method)) _ _
  rw [FormationSensitiveBasedIdentity.reflexivitySub_genericTerm]
  exact .rel _ _ (.root (FormationSensitiveBasedIdentity.authored_beta signature _ _ _ _))

theorem beta (input : Admitted context) :
    TermFibre.compare input.motive_reflexivity
      (tmSub input.j (project input.reflSection)) = input.base :=
  Subtype.ext input.beta_value

def reindex {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) : Admitted source where
  type := subst substitution.substitution input.type
  left := subst substitution.substitution input.left
  motive := subst substitution.substitution input.motive
  method := subst substitution.substitution input.method
  typed := by
    have composite : subComp substitution.substitution
        (identitySchemaSubstitution input.type input.left input.motive input.method) =
        identitySchemaSubstitution (subst substitution.substitution input.type)
          (subst substitution.substitution input.left) (subst substitution.substitution input.motive)
          (subst substitution.substitution input.method) := by
      funext index
      fin_cases index <;> rfl
    intro index
    rw [← composite, ← subst_subComp]
    exact (input.typed index).substitute substitution.typed

/-- The true binder-lifted native substitution, including the equality
witness binder, gives the admitted context map for a dependent motive. -/
def basedMap {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (input.reindex substitution).basedContext ⟶ input.basedContext where
  substitution := liftSub (liftSub substitution.substitution)
  typed := by
    have lifted := (substitution.typed.lift input.type).lift
      (.id (rename wk input.type) (rename wk input.left) (.var 0))
    simpa only [basedContext, reindex, FormationSensitiveBasedIdentity.basedContext,
      subst, subst_liftSub_wk, liftSub_zero] using lifted

theorem motive_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    tySub (QType.mk input.motiveType) (project (input.basedMap substitution)) =
      QType.mk (input.reindex substitution).motiveType := by
  apply (QType.mk_eq_iff _ _).mpr
  change Conv _ (subst (liftSub (liftSub substitution.substitution))
    (FormationSensitiveBasedIdentity.motiveBody input.motive))
    (FormationSensitiveBasedIdentity.motiveBody (subst substitution.substitution input.motive)) _
  simp only [FormationSensitiveBasedIdentity.motiveBody,
    FormationSensitiveBasedIdentity.doubleWeaken, subst, subst_liftSub_wk,
    liftSub_zero]
  exact .refl _

theorem j_substitution_value {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (tmSub input.j (project (input.basedMap substitution))).val =
      (input.reindex substitution).j.val := by
  apply (QTerm.mk_eq_iff _ _).mpr
  refine ⟨(QType.mk_eq_iff _ _).mp (input.motive_substitution substitution), ?_⟩
  change Conv _ (subst (liftSub (liftSub substitution.substitution))
    (FormationSensitiveBasedIdentity.genericTerm input.type input.left input.motive input.method))
    (FormationSensitiveBasedIdentity.genericTerm (subst substitution.substitution input.type)
      (subst substitution.substitution input.left) (subst substitution.substitution input.motive)
      (subst substitution.substitution input.method)) _
  simp only [FormationSensitiveBasedIdentity.genericTerm, subst_identityEliminateApp,
    FormationSensitiveBasedIdentity.doubleWeaken, subst_liftSub_wk, subst,
    liftSub_zero]
  exact .refl _

theorem j_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    TermFibre.compare (input.motive_substitution substitution)
      (tmSub input.j (project (input.basedMap substitution))) =
        (input.reindex substitution).j := Subtype.ext (input.j_substitution_value substitution)

theorem method_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (tmSub input.base (project substitution)).val = (input.reindex substitution).base.val := by
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨.refl _, .refl _⟩

theorem reflexivity_square {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (input.reindex substitution).reflSection ≫ input.basedMap substitution =
      substitution ≫ input.reflSection := by
  apply Hom.ext
  funext index
  refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
  · rfl
  · rfl
  · change subst (FormationSensitiveBasedIdentity.reflexivitySub
        (subst substitution.substitution input.left))
      (FormationSensitiveBasedIdentity.doubleWeaken (substitution.substitution older)) = _
    exact FormationSensitiveBasedIdentity.reflexivitySub_doubleWeaken _ _

/-- Reindexing the computed method and computing after the actual lifted
substitution give the same term class, with the reflexivity-context square
proved independently above. -/
theorem beta_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    totalSub (totalSub input.j.val (project input.reflSection)) (project substitution) =
      totalSub (input.reindex substitution).j.val
        (project (input.reindex substitution).reflSection) := by
  change totalSub (tmSub input.j (project input.reflSection)).val (project substitution) = _
  rw [input.beta_value]
  exact (input.method_substitution substitution).trans
    (input.reindex substitution).beta_value.symm

private theorem native_basedContext_eq (input : Admitted context) :
    extend (extend context input.element) (nativeWitness input.element input.leftTerm) =
      input.basedContext := by
  simp only [extend, nativeWitness, nativeId, TypeOver.reindex, Term.reindex,
    projectionHom, newest, element, leftTerm, subst_projection, basedContext,
    FormationSensitiveBasedIdentity.basedContext]

noncomputable def chosenContext (input : Admitted context) :
    QContext (OpaqueRelatorExtension.rules signature) :=
  chosenBasedContext input.element input.leftTerm

noncomputable def presentation (input : Admitted context) :
    _root_.CategoryTheory.Iso (C := QContext (OpaqueRelatorExtension.rules signature))
      input.chosenContext ((quotientProjection _).obj input.basedContext) :=
  (basedPresentation input.element input.leftTerm).trans
    (eqToIso (congrArg (quotientProjection _).obj input.native_basedContext_eq))

/-- The admitted native J inhabits the motive on the CwF's chosen based
context, transported along its proved presentation isomorphism. -/
noncomputable def chosenJ (input : Admitted context) :
    QuotientCwf.Tm _ (tySub (QType.mk input.motiveType) input.presentation.hom) :=
  tmSub input.j input.presentation.hom

noncomputable def chosenReflSection (input : Admitted context) :
    (quotientProjection (OpaqueRelatorExtension.rules signature)).obj context ⟶
      input.chosenContext :=
  project input.reflSection ≫ input.presentation.inv

theorem chosen_beta_value (input : Admitted context) :
    (tmSub input.chosenJ input.chosenReflSection).val = input.base.val := by
  change totalSub (totalSub input.j.val input.presentation.hom)
    (project input.reflSection ≫ input.presentation.inv) = _
  rw [← totalSub_comp, Category.assoc, input.presentation.inv_hom_id, Category.comp_id]
  exact input.beta_value

theorem chosen_motive_reflexivity (input : Admitted context) :
    tySub (tySub (QType.mk input.motiveType) input.presentation.hom) input.chosenReflSection =
      QType.mk input.methodType :=
  (tmSub input.chosenJ input.chosenReflSection).property.symm.trans
    ((congrArg QTerm.type input.chosen_beta_value).trans input.base.property)

theorem chosen_beta (input : Admitted context) :
    TermFibre.compare input.chosen_motive_reflexivity
      (tmSub input.chosenJ input.chosenReflSection) = input.base :=
  Subtype.ext input.chosen_beta_value

noncomputable def chosenMap {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (input.reindex substitution).chosenContext ⟶ input.chosenContext :=
  (input.reindex substitution).presentation.hom ≫ project (input.basedMap substitution) ≫
    input.presentation.inv

theorem chosen_j_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Admitted target) (substitution : source ⟶ target) :
    (tmSub input.chosenJ (input.chosenMap substitution)).val =
      (input.reindex substitution).chosenJ.val := by
  change totalSub (totalSub input.j.val input.presentation.hom)
    ((input.reindex substitution).presentation.hom ≫ project (input.basedMap substitution) ≫
      input.presentation.inv) = _
  rw [← totalSub_comp]
  simp only [Category.assoc, input.presentation.inv_hom_id, Category.comp_id]
  rw [totalSub_comp]
  exact congrArg (fun next => totalSub next (input.reindex substitution).presentation.hom)
    (input.j_substitution_value substitution)

end Admitted

/-! ## Coverage of arbitrary admitted native motive bodies -/

private theorem abstract_motive_beta {n : Nat} (body : Tower.Tm (n + 2))
    (right witness : Tower.Tm n) :
    Conv (OpaqueRelatorExtension.rules signature).headEq
      (.app (.app (.lam (.lam body)) right) witness)
      (subst (FormationSensitiveBasedIdentity.pointSub right witness) body)
      (OpaqueRelatorExtension.rules signature).computation := by
  have first : Conv (OpaqueRelatorExtension.rules signature).headEq
      (.app (.app (.lam (.lam body)) right) witness)
      (.app (.lam (subst (liftSub (subst0 right)) body)) witness)
      (OpaqueRelatorExtension.rules signature).computation :=
    .rel _ _ (.congAppFun (.betaPi _ _))
  have second : Conv (OpaqueRelatorExtension.rules signature).headEq
      (.app (.lam (subst (liftSub (subst0 right)) body)) witness)
      (subst (subst0 witness) (subst (liftSub (subst0 right)) body))
      (OpaqueRelatorExtension.rules signature).computation := .rel _ _ (.betaPi _ _)
  have substitutions : subComp (subst0 witness) (liftSub (subst0 right)) =
      FormationSensitiveBasedIdentity.pointSub right witness := by
    funext index
    refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
    · rfl
    · exact inst0_rename_wk witness right
    · rfl
  rw [subst_subComp, substitutions] at second
  exact .trans _ _ _ first second

/-- Every native motive body formed at the declaration's motive universe
is covered, including motives depending on both the endpoint and path.
The double lambda is actually typed; beta converts the independently
supplied method into the declaration's method annotation. -/
def ofBody {context : Context (OpaqueRelatorExtension.rules signature)}
    (type left : Tower.Tm context.arity)
    (typeFormed : Typing (OpaqueRelatorExtension.rules signature) context.raw
      type (sortTm elementLevel))
    (leftTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw left type)
    (body : Tower.Tm (context.arity + 2))
    (bodyFormed : Typing (OpaqueRelatorExtension.rules signature)
      (FormationSensitiveBasedIdentity.basedContext context.raw type left)
      body (sortTm motiveLevel))
    (method : Tower.Tm context.arity)
    (methodTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body)) : Admitted context where
  type := type
  left := left
  motive := .lam (.lam body)
  method := method
  typed := by
    have empty : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
        .nil context.raw emptySchemaSubstitution := fun index => Fin.elim0 index
    have element : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
        contextA context.raw (elementSchemaSubstitution type) := empty.extend typeFormed
    have point : FormationSensitive.CtxMor (OpaqueRelatorExtension.rules signature)
        contextAX context.raw (consSub left (elementSchemaSubstitution type)) :=
      element.extend leftTyped
    have motiveFormation := (OpaqueRelatorExtension.relator_typing
      FormationSensitiveNativeIdentity.identityMotiveType_hasType).substitute point
    obtain ⟨_, _, _, _, _, innerFormed, innerUniverse, _⟩ := motiveFormation.piFormation
    have motiveTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw
        (.lam (.lam body))
        (subst (consSub left (elementSchemaSubstitution type)) identityMotiveType) :=
      .lamIntro motiveFormation (.sort identityMotiveLevel)
        (.lamIntro innerFormed innerUniverse bodyFormed)
    have motive := point.extend motiveTyped
    have methodFormation := (OpaqueRelatorExtension.relator_typing
      FormationSensitiveNativeIdentity.identityReflCaseType_hasType).substitute motive
    exact motive.extend (.conv methodTyped methodFormation (.sort motiveLevel)
      (abstract_motive_beta body left (.refl left)).symm)

theorem ofBody_covers {context : Context (OpaqueRelatorExtension.rules signature)}
    (type left : Tower.Tm context.arity)
    (typeFormed : Typing (OpaqueRelatorExtension.rules signature) context.raw
      type (sortTm elementLevel))
    (leftTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw left type)
    (body : Tower.Tm (context.arity + 2))
    (bodyFormed : Typing (OpaqueRelatorExtension.rules signature)
      (FormationSensitiveBasedIdentity.basedContext context.raw type left)
      body (sortTm motiveLevel))
    (method : Tower.Tm context.arity)
    (methodTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw method
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) body)) :
    let input := ofBody type left typeFormed leftTyped body bodyFormed method methodTyped
    ∃ actual : TypeOver input.basedContext, actual.code = body ∧
      actual.level = .sort motiveLevel ∧ QType.mk input.motiveType = QType.mk actual := by
  let actual : TypeOver
      (ofBody type left typeFormed leftTyped body bodyFormed method methodTyped).basedContext :=
    ⟨body, .sort motiveLevel, .sort motiveLevel, bodyFormed⟩
  refine ⟨actual, rfl, rfl, ?_⟩
  apply (QType.mk_eq_iff _ _).mpr
  have beta := abstract_motive_beta (signature := signature)
    (subst (liftSub (liftSub (fun index => .var (wk (wk index))))) body)
    (.var 1) (.var 0)
  change Conv _ (.app (.app (.lam (.lam _)) (.var 1)) (.var 0)) body _
  convert beta using 1
  · apply congrArg (fun next : Tower.Tm (context.arity + 2 + 2) =>
      (.app (.app (.lam (.lam next)) (.var 1)) (.var 0) : Tower.Tm (context.arity + 2)))
    rw [rename_comp]
    change rename _ body = subst (liftSub (liftSub (renSub (fun index => wk (wk index))))) body
    rw [liftSub_renSub, liftSub_renSub, subst_renSub]
    apply rename_ext
    intro index
    refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
    · rfl
    · rfl
    · rfl
  · rw [subst_subComp]
    have same : subComp (FormationSensitiveBasedIdentity.pointSub
        (.var 1 : Tower.Tm (context.arity + 2)) (.var 0))
        (liftSub (liftSub (fun index : Fin context.arity =>
          (Presentation.Tm.var (wk (wk index)) : Tower.Tm (context.arity + 2))))) = ids := by
      funext index
      refine Fin.cases ?_ (fun prior => Fin.cases ?_ (fun older => ?_) prior) index
      · rfl
      · rfl
      · rfl
    rw [same, subst_ids]

/-- Within a fixed admitted endpoint context, changing the formed motive
body and method by native conversion does not change the resulting J class.
Thus motive/branch representative choice is not an extra observation of
this operation; both the result annotation and result code are compared. -/
theorem ofBody_j_congruent {context : Context (OpaqueRelatorExtension.rules signature)}
    (type left : Tower.Tm context.arity)
    (typeFormed : Typing (OpaqueRelatorExtension.rules signature) context.raw
      type (sortTm elementLevel))
    (leftTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw left type)
    (firstBody secondBody : Tower.Tm (context.arity + 2))
    (firstFormed : Typing (OpaqueRelatorExtension.rules signature)
      (FormationSensitiveBasedIdentity.basedContext context.raw type left) firstBody (sortTm motiveLevel))
    (secondFormed : Typing (OpaqueRelatorExtension.rules signature)
      (FormationSensitiveBasedIdentity.basedContext context.raw type left) secondBody (sortTm motiveLevel))
    (firstMethod secondMethod : Tower.Tm context.arity)
    (firstTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw firstMethod
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) firstBody))
    (secondTyped : Typing (OpaqueRelatorExtension.rules signature) context.raw secondMethod
      (subst (FormationSensitiveBasedIdentity.reflexivitySub left) secondBody))
    (bodies : Conv (OpaqueRelatorExtension.rules signature).headEq firstBody secondBody
      (OpaqueRelatorExtension.rules signature).computation)
    (methods : Conv (OpaqueRelatorExtension.rules signature).headEq firstMethod secondMethod
      (OpaqueRelatorExtension.rules signature).computation) :
    QTerm.mk (ofBody type left typeFormed leftTyped firstBody firstFormed firstMethod firstTyped).nativeJ =
      QTerm.mk (ofBody type left typeFormed leftTyped secondBody secondFormed secondMethod secondTyped).nativeJ := by
  have motives := (Conv.congLam (Conv.congLam bodies)).renameTerms wk |>.renameTerms wk
  have methods := methods.renameTerms wk |>.renameTerms wk
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨Conv.congApp (Conv.congApp motives (.refl _)) (.refl _),
    Conv.congApp (Conv.congApp (Conv.congApp (Conv.congApp
      (Conv.congApp (Conv.congApp (.refl _) (.refl _)) (.refl _)) motives) methods)
      (.refl _)) (.refl _)⟩

end Based

/-! ## The fixed declaration does not provide arbitrary-level elimination -/

namespace LevelBoundary

variable {signature : Declaration.Signature Tower.Head}

private theorem sort_typing_lower_aux (opacity : OpaqueRelatorExtension.Opacity signature)
    {n : Nat} {context : Tower.Ctx n} {term type : Tower.Tm n}
    (typed : Typing (OpaqueRelatorExtension.rules signature) context term type) :
    ∀ level, term = sortTm level → ∀ upper,
      Conv (OpaqueRelatorExtension.rules signature).headEq type (sortTm upper)
        (OpaqueRelatorExtension.rules signature).computation →
      ∀ valuation, LevelExpr.eval valuation level + 1 ≤ LevelExpr.eval valuation upper := by
  induction typed with
  | headType head =>
      intro level same upper converted valuation
      change Tower.HeadTyping _ _ at head
      cases head with
      | legacyGround => cases same
      | sort original =>
          cases same
          have equality := (QuotientUniverses.sort_conversion_iff opacity (.succ level) upper).mp
            converted valuation
          exact Nat.le_of_eq equality
  | @cumul n context term lower upper typed order ih =>
      intro level same final converted valuation
      change Tower.Cumulative lower upper at order
      cases lower with
      | legacyGround => cases order
      | sort lower =>
          cases upper with
          | legacyGround => cases order
          | sort upper =>
              have before := ih level same lower (.refl _) valuation
              have equality := (QuotientUniverses.sort_conversion_iff opacity upper final).mp
                converted valuation
              exact (before.trans (order valuation)).trans (Nat.le_of_eq equality)
  | conv _ _ _ converted ih _ =>
      intro level same upper final valuation
      exact ih level same upper (.trans _ _ _ converted final) valuation
  | _ => intro level same; cases same

/-- A lower bound for the actual refined typing derivation, including all
its conversion and cumulative tails. Opacity is used only in the proved
universe-conversion invariant, not as an assumed typing rule. -/
theorem sort_typing_lower_bound (opacity : OpaqueRelatorExtension.Opacity signature)
    {n : Nat} {context : Tower.Ctx n} {level upper : LevelExpr Nat}
    (typed : Typing (OpaqueRelatorExtension.rules signature) context
      (sortTm level) (sortTm upper)) (valuation : Nat → Nat) :
    LevelExpr.eval valuation level + 1 ≤ LevelExpr.eval valuation upper :=
  sort_typing_lower_aux opacity typed level rfl upper (.refl _) valuation

theorem sort_not_typed_at_self (opacity : OpaqueRelatorExtension.Opacity signature)
    {n : Nat} (context : Tower.Ctx n) (level : LevelExpr Nat) :
    ¬ Typing (OpaqueRelatorExtension.rules signature) context (sortTm level) (sortTm level) := by
  intro typed
  exact Nat.not_succ_le_self _ (sort_typing_lower_bound opacity typed (fun _ => 0))

/-- Forming identity at this larger domain is possible, but passing that
same universe as the first argument of the fixed J declaration is not. -/
theorem no_j_on_own_element_universe (opacity : OpaqueRelatorExtension.Opacity signature)
    {n : Nat} {context : Tower.Ctx n}
    (left motive method right witness displayed : Tower.Tm n) :
    ¬ Judgment (OpaqueRelatorExtension.rules signature) context
      (NativeIndexedFamilies.Intrinsic.identityEliminateApp
        (sortTm NativeIndexedFamilies.Intrinsic.elementLevel)
        left motive method right witness) displayed := by
  intro admitted
  have parameters := (FormationSensitiveBasedIdentity.arguments_of_judgment opacity admitted).1
  exact sort_not_typed_at_self opacity context _
    (FormationSensitiveBasedIdentity.parameters_type parameters)

def largeDomain (context : Context (OpaqueRelatorExtension.rules signature)) : TypeOver context :=
  QuotientUniverses.universeType context NativeIndexedFamilies.Intrinsic.elementLevel

def largePoint (context : Context (OpaqueRelatorExtension.rules signature)) :
    Term context (largeDomain context) :=
  ⟨.head .legacyGround, .cumul (.headType .legacyGround) (fun _ => Nat.zero_le _)⟩

theorem identity_exists_beyond_fixed_j (opacity : OpaqueRelatorExtension.Opacity signature)
    (context : Context (OpaqueRelatorExtension.rules signature)) :
    Judgment (OpaqueRelatorExtension.rules signature) context.raw
        (nativeRefl (largePoint context)).code
        (nativeId (largeDomain context) (largePoint context) (largePoint context)).code ∧
      ¬ ∃ input : Based.Admitted context, input.type = (largeDomain context).code := by
  refine ⟨(nativeRefl (largePoint context)).judgment, ?_⟩
  rintro ⟨input, same⟩
  have typed := FormationSensitiveBasedIdentity.parameters_type input.parameters
  rw [same] at typed
  exact sort_not_typed_at_self opacity context.raw _ typed

theorem higher_motive_is_formed_but_not_admitted
    (opacity : OpaqueRelatorExtension.Opacity signature)
    (context : Context (OpaqueRelatorExtension.rules signature)) :
    Judgment (OpaqueRelatorExtension.rules signature) context.raw
        (sortTm NativeIndexedFamilies.Intrinsic.motiveLevel)
        (sortTm (.succ NativeIndexedFamilies.Intrinsic.motiveLevel)) ∧
      ¬ Typing (OpaqueRelatorExtension.rules signature) context.raw
        (sortTm NativeIndexedFamilies.Intrinsic.motiveLevel)
        (sortTm NativeIndexedFamilies.Intrinsic.motiveLevel) :=
  ⟨⟨context.formed, .headType (.sort _)⟩, sort_not_typed_at_self opacity context.raw _⟩

end LevelBoundary

/-! ## Actual common-environment controls -/

namespace Controls

open NativeIndexedFamilies.Intrinsic

/-- This body depends on both the varying endpoint (inside its path type)
and the path itself. Its fixed left endpoint is the actual mixed HOL-list
and wire projection, not a separately invented evaluator. -/
def mixedBody (wire : NativeWireData.Wire) : Tower.Tm 2 :=
  .id (.id NativeWireData.dataType
    (FormationSensitiveBasedIdentity.doubleWeaken (Common.projected wire).code) (.var 1))
    (.var 0) (.var 0)

theorem mixedBody_formed (wire : NativeWireData.Wire) :
    Typing HOLNativeRelatorCompatibility.rules
      (FormationSensitiveBasedIdentity.basedContext Common.context.raw NativeWireData.dataType
        (Common.projected wire).code) (mixedBody wire) (sortTm motiveLevel) := by
  have leftTyped : Typing HOLNativeRelatorCompatibility.rules
      (FormationSensitiveBasedIdentity.basedContext Common.context.raw NativeWireData.dataType
        (Common.projected wire).code)
      (FormationSensitiveBasedIdentity.doubleWeaken (Common.projected wire).code)
      NativeWireData.dataType := (Common.projected wire).typed.weaken.weaken
  have pathType : Typing HOLNativeRelatorCompatibility.rules
      (FormationSensitiveBasedIdentity.basedContext Common.context.raw NativeWireData.dataType
        (Common.projected wire).code)
      (.id NativeWireData.dataType
        (FormationSensitiveBasedIdentity.doubleWeaken (Common.projected wire).code) (.var 1))
      (sortTm Tower.zero) :=
    .idForm (HOLNativeRelatorCompatibility.wire_typing (NativeWireData.dataType_formed _))
      (.sort Tower.zero) leftTyped (.var 1)
  exact .cumul (.idForm pathType (.sort Tower.zero) (.var 0) (.var 0)) (fun _ => Nat.zero_le _)

theorem mixedMethod_typed (wire : NativeWireData.Wire) :
    Typing HOLNativeRelatorCompatibility.rules Common.context.raw
      (.refl (.refl (Common.projected wire).code))
      (subst (FormationSensitiveBasedIdentity.reflexivitySub (Common.projected wire).code)
        (mixedBody wire)) := by
  change Typing _ _ _ (.id (.id NativeWireData.dataType
    (subst (FormationSensitiveBasedIdentity.reflexivitySub (Common.projected wire).code)
      (FormationSensitiveBasedIdentity.doubleWeaken (Common.projected wire).code))
    (Common.projected wire).code) (.refl (Common.projected wire).code) (.refl (Common.projected wire).code))
  rw [FormationSensitiveBasedIdentity.reflexivitySub_doubleWeaken]
  exact .reflIntro (.reflIntro (Common.projected wire).typed)

def mixedInput (wire : NativeWireData.Wire) :
    Based.Admitted (signature := HOLNativeRelatorCompatibility.signature) Common.context :=
  Based.ofBody NativeWireData.dataType (Common.projected wire).code
    (.cumul Common.wireType.formed (fun _ => Nat.zero_le _)) (Common.projected wire).typed
    (mixedBody wire) (mixedBody_formed wire) (.refl (.refl (Common.projected wire).code))
    (mixedMethod_typed wire)

theorem mixed_body_coverage (wire : NativeWireData.Wire) :
    ∃ actual : TypeOver (mixedInput wire).basedContext,
      actual.code = mixedBody wire ∧ actual.level = .sort motiveLevel ∧
        QType.mk (mixedInput wire).motiveType = QType.mk actual :=
  Based.ofBody_covers _ _ _ _ _ _ _ _

theorem mixed_constructor_class (wire : NativeWireData.Wire) :
    QType.mk (nativeId Common.wireType (Common.projected wire) (Common.projected wire)) =
      QType.mk (nativeId Common.wireType (Common.result wire) (Common.result wire)) ∧
    QTerm.mk (nativeRefl (Common.projected wire)) = QTerm.mk (nativeRefl (Common.result wire)) := by
  have same := Common.projected_converts_result wire
  have identities := Conv.congId (.refl Common.wireType.code) same same
  exact ⟨(QType.mk_eq_iff _ _).mpr identities,
    (QTerm.mk_eq_iff _ _).mpr ⟨identities,
      Conv.mapCompatible Presentation.Tm.refl (fun step => .congRefl step) same⟩⟩

/-- The two-binder map in this instance is a real weakening into an
additional formed Data context. The method and path-dependent family are
not replaced by constants in the substitution square. -/
theorem mixed_weakening_square (wire : NativeWireData.Wire) :
    ((mixedInput wire).reindex (projectionHom Common.context Common.wireType)).reflSection ≫
        (mixedInput wire).basedMap (projectionHom Common.context Common.wireType) =
      projectionHom Common.context Common.wireType ≫ (mixedInput wire).reflSection ∧
      (tmSub (mixedInput wire).chosenJ
        ((mixedInput wire).chosenMap (projectionHom Common.context Common.wireType))).val =
      ((mixedInput wire).reindex (projectionHom Common.context Common.wireType)).chosenJ.val :=
  ⟨(mixedInput wire).reflexivity_square _, (mixedInput wire).chosen_j_substitution _⟩

theorem mixed_j_crown (wire : NativeWireData.Wire) :
    Judgment HOLNativeRelatorCompatibility.rules (mixedInput wire).basedContext.raw
        (mixedInput wire).nativeJ.code (mixedInput wire).motiveType.code ∧
      (tmSub (mixedInput wire).chosenJ (mixedInput wire).chosenReflSection).val =
        (mixedInput wire).base.val ∧
      QTerm.mk (nativeRefl (Common.projected wire)) = QTerm.mk (nativeRefl (Common.result wire)) ∧
      QTerm.mk (Common.result (.natural 7)) ≠ QTerm.mk (Common.result (.natural 8)) :=
  ⟨(mixedInput wire).nativeJ.judgment, (mixedInput wire).chosen_beta_value,
    (mixed_constructor_class wire).2, FibreControls.seven_eight_distinct⟩

theorem actual_identity_scope_boundary :
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
        (nativeRefl (LevelBoundary.largePoint Common.context)).code
        (nativeId (LevelBoundary.largeDomain Common.context)
          (LevelBoundary.largePoint Common.context) (LevelBoundary.largePoint Common.context)).code ∧
      ¬ ∃ input : Based.Admitted (signature := HOLNativeRelatorCompatibility.signature) Common.context,
        input.type = (LevelBoundary.largeDomain Common.context).code :=
  LevelBoundary.identity_exists_beyond_fixed_j HOLNativeRelatorCompatibility.opacity Common.context

end Controls

end FormationSensitiveContextual.QuotientIdentity
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
