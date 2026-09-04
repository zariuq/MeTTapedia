import Mettapedia.Computability.SplitReadoutComparison
import Mettapedia.GSLT.Core.ContextualTypeCategory
import Mettapedia.TypeTheory.SelectedModalIntroduction

/-!
# Contextual objects, explicit instantiation, and selected code splicing

A contextual object packages a term together with the local context on which
it may depend.  Ordinary substitution in an ambient context leaves such a
package unchanged; using its open variables requires an explicit contextual
substitution.  Rebinding along an isomorphism of contexts is the structural
core of hygienic freshening.

At the modal term level, quotation and splicing are independent capabilities.
A beta law makes splicing a split readout from code to bodies.  The stronger
eta law is exactly faithfulness of that readout, hence exactly the condition
for a globally lossless computational-trinity comparison.  Without eta,
quotation still selects an exact canonical fragment while code may retain
routes, provenance, occurrence identity, or other intensional information.

These interfaces do not choose a syntax representation, variable-identity
scheme, staging calculus, evaluation policy, or surface quote form.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCode

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.SelectedModalIntroduction
open Mettapedia.TypeTheory.ExtensionalReadout

universe u v w w' uObservation

/-! ## Contextual objects over a CwF -/

/-- A term together with the local context and type on which it depends.
This is the semantic shape of a contextual object `context ⊢ term : type`.
No ambient context or quotation constructor is included. -/
structure ContextualObject (C : Cwf.{u, v, w, w'}) where
  localContext : C.Ctx
  objectType : C.Ty localContext
  objectTerm : C.Tm localContext objectType

namespace ContextualObject

variable {C : Cwf.{u, v, w, w'}}

/-- Explicitly instantiate every open variable of a contextual object. -/
def instantiate (object : ContextualObject C) {context : C.Ctx}
    (substitution : C.Sub context object.localContext) :
    C.Tm context (C.tySub object.objectType substitution) :=
  C.tmSub object.objectTerm substitution

/-- Reindex the complete contextual object along an explicit substitution. -/
def reindex (object : ContextualObject C) {context : C.Ctx}
    (substitution : C.Sub context object.localContext) :
    ContextualObject C where
  localContext := context
  objectType := C.tySub object.objectType substitution
  objectTerm := object.instantiate substitution

@[simp] theorem reindex_localContext (object : ContextualObject C)
    {context : C.Ctx} (substitution : C.Sub context object.localContext) :
    (object.reindex substitution).localContext = context :=
  rfl

@[simp] theorem reindex_objectType (object : ContextualObject C)
    {context : C.Ctx} (substitution : C.Sub context object.localContext) :
    (object.reindex substitution).objectType =
      C.tySub object.objectType substitution :=
  rfl

/-- Instantiation by the identity substitution recovers the stored term,
up to the CwF's required transport along type-substitution identity. -/
theorem instantiate_identity (object : ContextualObject C) :
    object.instantiate (C.idS object.localContext) =
      cast (by rw [C.tySub_id]) object.objectTerm :=
  C.tmSub_id object.objectTerm

/-- Explicit contextual instantiation composes exactly as CwF term
substitution. -/
theorem instantiate_comp {first middle : C.Ctx}
    (object : ContextualObject C)
    (later : C.Sub middle object.localContext)
    (earlier : C.Sub first middle) :
    object.instantiate (C.compS later earlier) =
      cast (by rw [C.tySub_comp])
        (C.tmSub (object.instantiate later) earlier) :=
  C.tmSub_comp object.objectTerm later earlier

/-- A raw context as an object of the CwF's base category. -/
abbrev baseContext (C : Cwf.{u, v, w, w'}) (context : C.Ctx) :
    C.base.Context :=
  ⟨context⟩

/-- Hygienic freshening at this abstraction level is reindexing along an
isomorphism of contexts.  It changes the context names/positions without
discarding contextual information. -/
def freshen (object : ContextualObject C) {freshContext : C.Ctx}
    (contextIso : baseContext C freshContext ≅
      baseContext C object.localContext) :
    ContextualObject C :=
  object.reindex contextIso.hom

/-- Instantiating a freshly rebound object with the inverse renaming recovers
the original term heterogeneously.  The heterogeneous statement retains the
explicit type transports rather than imposing a definitional-equality
convention. -/
theorem instantiate_freshen_inverse (object : ContextualObject C)
    {freshContext : C.Ctx}
    (contextIso : baseContext C freshContext ≅
      baseContext C object.localContext) :
    HEq
      ((object.freshen contextIso).instantiate contextIso.inv)
      object.objectTerm := by
  have compositionIsIdentity :
      C.compS contextIso.hom contextIso.inv =
        C.idS object.localContext := by
    exact contextIso.inv_hom_id
  have compositionLaw :=
    TypeOver.tmSub_comp_heq
      object.objectTerm contextIso.hom contextIso.inv
  have identityLaw :
      HEq
        (C.tmSub object.objectTerm
          (C.compS contextIso.hom contextIso.inv))
        object.objectTerm := by
    rw [compositionIsIdentity]
    exact (heq_of_eq (C.tmSub_id object.objectTerm)).trans
      (cast_heq _ object.objectTerm)
  exact compositionLaw.symm.trans identityLaw

/-! ## Ambient substitution does not instantiate held code -/

/-- A contextual object held in an ambient context.  The ambient index is
deliberately phantom: the package is closed with respect to ambient ordinary
variables, while remaining open in its own `localContext`. -/
abbrev Held (C : Cwf.{u, v, w, w'}) (_ambient : C.Ctx) :=
  ContextualObject C

namespace Held

/-- Ordinary substitution in the ambient context leaves held contextual
code unchanged. -/
def ambientSubstitution {source target : C.Ctx}
    (object : Held C target) (_substitution : C.Sub source target) :
    Held C source :=
  object

@[simp] theorem ambientSubstitution_identity {context : C.Ctx}
    (object : Held C context) :
    ambientSubstitution object (C.idS context) = object :=
  rfl

@[simp] theorem ambientSubstitution_comp {first middle last : C.Ctx}
    (object : Held C last) (later : C.Sub middle last)
    (earlier : C.Sub first middle) :
    ambientSubstitution object (C.compS later earlier) =
      ambientSubstitution (ambientSubstitution object later) earlier :=
  rfl

end Held

/-! ## A material substitution-boundary control -/

namespace FamiliesCanary

abbrev FamilyCwf := familiesCwf.{0}

/-- Open Boolean code whose result is its one local Boolean variable. -/
def booleanObject : ContextualObject FamilyCwf where
  localContext := Bool
  objectType := fun _ => Bool
  objectTerm := fun value => value

def selectFalse : FamilyCwf.Sub PUnit Bool := fun _ => false
def selectTrue : FamilyCwf.Sub PUnit Bool := fun _ => true

/-- The same object may be held under an unrelated Boolean ambient context. -/
def heldBooleanObject : Held FamilyCwf Bool := booleanObject

/-- Ambient substitution cannot instantiate the code, while explicit
contextual substitutions select observably different bodies. -/
theorem ambient_stops_explicit_instantiation_enters :
    Held.ambientSubstitution heldBooleanObject selectFalse =
        Held.ambientSubstitution heldBooleanObject selectTrue /\
      booleanObject.instantiate selectFalse PUnit.unit ≠
        booleanObject.instantiate selectTrue PUnit.unit := by
  constructor
  · rfl
  · change false ≠ true
    exact Bool.false_ne_true

end FamiliesCanary

end ContextualObject

/-! ## Selected modal splicing -/

/-- Elimination from modal code along only a selected class of modalities.
It is deliberately separate from quotation: a modal type former and its term
introduction do not manufacture execution or unquotation. -/
structure SelectedSpliceTermStructure (modes : ModeTheory)
    (cwf : ModalCwF modes) (laws : ModalCwFLaws modes cwf)
    (selection : WideSubtheory modes) where
  splice : {high low : modes.Mode} -> (modality : modes.Hom high low) ->
    selection.selected modality ->
    {context : cwf.Con low} ->
    {type : cwf.Ty (cwf.lock modality context)} ->
    cwf.Tm context (cwf.boxTy modality type) ->
      cwf.Tm (cwf.lock modality context) type
  splice_sub : forall {high low : modes.Mode}
    (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {first last : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality last)}
    (code : cwf.Tm last (cwf.boxTy modality type))
    (substitution : cwf.Sub first last),
    HEq
      (splice modality admitted
        (cwf.castTm (laws.boxTy_natural modality type substitution)
          (cwf.tmSub code substitution)))
      (cwf.tmSub (splice modality admitted code)
        (laws.lockSub modality substitution))
  splice_id : forall {mode : modes.Mode} {context : cwf.Con mode}
    {type : cwf.Ty (cwf.lock (modes.id mode) context)}
    (code : cwf.Tm context (cwf.boxTy (modes.id mode) type)),
    HEq
      (splice (modes.id mode) (selection.identity_selected mode) code)
      code

/-- Quote-then-splice beta.  It says every body is represented by its
quotation, not that every code is determined by its body. -/
structure SelectedQuoteSpliceBeta (modes : ModeTheory)
    (cwf : ModalCwF modes) (laws : ModalCwFLaws modes cwf)
    (selection : WideSubtheory modes)
    (quotation : SelectedQuotationTermStructure modes cwf laws selection)
    (splicing : SelectedSpliceTermStructure modes cwf laws selection) where
  splice_quote : forall {high low : modes.Mode}
    (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    (term : cwf.Tm (cwf.lock modality context) type),
    splicing.splice modality admitted
        (quotation.introduce modality admitted term) = term

/-- Splice-then-quote eta.  This is the additional assertion that code has no
intensional information beyond the body recovered by splicing. -/
structure SelectedQuoteSpliceEta (modes : ModeTheory)
    (cwf : ModalCwF modes) (laws : ModalCwFLaws modes cwf)
    (selection : WideSubtheory modes)
    (quotation : SelectedQuotationTermStructure modes cwf laws selection)
    (splicing : SelectedSpliceTermStructure modes cwf laws selection) where
  quote_splice : forall {high low : modes.Mode}
    (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    (code : cwf.Tm context (cwf.boxTy modality type)),
    quotation.introduce modality admitted
        (splicing.splice modality admitted code) = code

namespace SelectedQuoteSpliceBeta

variable {modes : ModeTheory} {cwf : ModalCwF modes}
variable {laws : ModalCwFLaws modes cwf}
variable {selection : WideSubtheory modes}
variable {quotation : SelectedQuotationTermStructure modes cwf laws selection}
variable {splicing : SelectedSpliceTermStructure modes cwf laws selection}

/-- Beta makes quotation injective at every selected fibre: executable code
cannot identify two bodies and still splice both back exactly. -/
theorem quotation_injective
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Function.Injective
      (quotation.introduce modality admitted :
        cwf.Tm (cwf.lock modality context) type ->
          cwf.Tm context (cwf.boxTy modality type)) := by
  intro left right sameCode
  calc
    left = splicing.splice modality admitted
        (quotation.introduce modality admitted left) :=
      (beta.splice_quote modality admitted left).symm
    _ = splicing.splice modality admitted
        (quotation.introduce modality admitted right) :=
      congrArg (splicing.splice modality admitted) sameCode
    _ = right := beta.splice_quote modality admitted right

/-- Beta makes splicing surjective onto bodies: every body is obtained by
splicing its quotation. -/
theorem splicing_surjective
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Function.Surjective
      (splicing.splice modality admitted :
        cwf.Tm context (cwf.boxTy modality type) ->
          cwf.Tm (cwf.lock modality context) type) := by
  intro body
  exact ⟨quotation.introduce modality admitted body,
    beta.splice_quote modality admitted body⟩

/-- Beta and eta together exhibit an actual equivalence between code and
body at the selected fibre. -/
def codeBodyEquiv
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    (eta : SelectedQuoteSpliceEta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    cwf.Tm context (cwf.boxTy modality type) ≃
      cwf.Tm (cwf.lock modality context) type where
  toFun := splicing.splice modality admitted
  invFun := quotation.introduce modality admitted
  left_inv := eta.quote_splice modality admitted
  right_inv := beta.splice_quote modality admitted

/-- Beta turns code-to-body splicing into a split extensional readout whose
selected representatives are quotations. -/
def readout (beta : SelectedQuoteSpliceBeta modes cwf laws selection
    quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    SplitReadout
      (cwf.Tm context (cwf.boxTy modality type))
      (cwf.Tm (cwf.lock modality context) type) where
  observe := splicing.splice modality admitted
  representative := quotation.introduce modality admitted
  observe_representative := beta.splice_quote modality admitted

/-- At a selected fibre, eta is exactly faithfulness of the beta readout. -/
theorem faithful_iff_quote_splice
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    (beta.readout modality admitted (context := context) (type := type)).Faithful
      <->
      forall code : cwf.Tm context (cwf.boxTy modality type),
        quotation.introduce modality admitted
            (splicing.splice modality admitted code) = code := by
  simpa [readout, SplitReadout.canonicalize] using
    SplitReadout.faithful_iff_canonicalize_eq
      (beta.readout modality admitted (context := context) (type := type))

/-- Every beta code interface has an exact computational-trinity comparison
on its canonical quotations. -/
def canonicalExactComparison
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :=
  Mettapedia.Computability.SplitReadoutComparison.canonicalExactComparison
    (beta.readout modality admitted (context := context) (type := type))

/-- The induced code/body comparison loses no information exactly when the
splice readout is eta-faithful. -/
theorem comparison_not_loses_iff_quote_splice
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    (¬ (Mettapedia.Computability.SplitReadoutComparison.comparison
        (beta.readout modality admitted (context := context) (type := type))).LosesProgramInformation) <->
      forall code : cwf.Tm context (cwf.boxTy modality type),
        quotation.introduce modality admitted
            (splicing.splice modality admitted code) = code := by
  rw [Mettapedia.Computability.SplitReadoutComparison.not_loses_iff_faithful]
  exact beta.faithful_iff_quote_splice modality admitted

/-- An observation of code descends to an observation of the spliced body
exactly when it cannot distinguish two codes with the same splice result.
This is the observer boundary between extensional bodies and retained
intensional code information. -/
theorem observer_factors_through_splice_iff_fibreInvariant
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)}
    {Observation : Type uObservation}
    (observer : cwf.Tm context (cwf.boxTy modality type) -> Observation) :
    (exists summarize : cwf.Tm (cwf.lock modality context) type -> Observation,
        forall code,
          summarize (splicing.splice modality admitted code) = observer code) <->
      (forall {left right},
        splicing.splice modality admitted left =
            splicing.splice modality admitted right ->
          observer left = observer right) := by
  simpa only [readout, SplitReadout.FactorsObserver,
    SplitReadout.FibreInvariant] using
      SplitReadout.factorsObserver_iff_fibreInvariant
        (beta.readout modality admitted (context := context) (type := type))
        observer

/-- Eta is also exactly the assertion that the complete code identity
observation descends through splicing.  Thus a globally exact code/body
interface has no observer-visible code information beyond its body. -/
theorem identity_observer_factors_iff_quote_splice
    (beta : SelectedQuoteSpliceBeta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    SplitReadout.FactorsObserver
        (beta.readout modality admitted (context := context) (type := type))
        (fun code => code) <->
      forall code : cwf.Tm context (cwf.boxTy modality type),
        quotation.introduce modality admitted
            (splicing.splice modality admitted code) = code := by
  rw [SplitReadout.factorsObserver_iff_fibreInvariant]
  change
    (beta.readout modality admitted (context := context) (type := type)).Faithful <-> _
  exact beta.faithful_iff_quote_splice modality admitted

end SelectedQuoteSpliceBeta

namespace SelectedQuoteSpliceEta

variable {modes : ModeTheory} {cwf : ModalCwF modes}
variable {laws : ModalCwFLaws modes cwf}
variable {selection : WideSubtheory modes}
variable {quotation : SelectedQuotationTermStructure modes cwf laws selection}
variable {splicing : SelectedSpliceTermStructure modes cwf laws selection}

/-- Eta makes splicing injective: no two codes may execute to the same body. -/
theorem splicing_injective
    (eta : SelectedQuoteSpliceEta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Function.Injective
      (splicing.splice modality admitted :
        cwf.Tm context (cwf.boxTy modality type) ->
          cwf.Tm (cwf.lock modality context) type) := by
  intro left right sameBody
  calc
    left = quotation.introduce modality admitted
        (splicing.splice modality admitted left) :=
      (eta.quote_splice modality admitted left).symm
    _ = quotation.introduce modality admitted
        (splicing.splice modality admitted right) :=
      congrArg (quotation.introduce modality admitted) sameBody
    _ = right := eta.quote_splice modality admitted right

/-- Eta makes quotation surjective onto code. -/
theorem quotation_surjective
    (eta : SelectedQuoteSpliceEta modes cwf laws selection
      quotation splicing)
    {high low : modes.Mode} (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {context : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality context)} :
    Function.Surjective
      (quotation.introduce modality admitted :
        cwf.Tm (cwf.lock modality context) type ->
          cwf.Tm context (cwf.boxTy modality type)) := by
  intro code
  exact ⟨splicing.splice modality admitted code,
    eta.quote_splice modality admitted code⟩

end SelectedQuoteSpliceEta

/-! ## A nontrivial identity-modal function model -/

namespace FunctionModel

/-- The terminal mode theory.  Its sole modality is identity, so this model is
a law-bearing control for contextual code rather than a claim about staging. -/
def modes : ModeTheory where
  Mode := PUnit
  Hom := fun _ _ => PUnit
  id := fun _ => PUnit.unit
  comp := fun _ _ => PUnit.unit
  id_comp := fun _ => rfl
  comp_id := fun _ => rfl
  comp_assoc := fun _ _ _ => rfl

/-- A simple function CwF with arbitrary small contexts, types, and terms.
Locking and boxing along the only modality are identity operations. -/
def cwf : ModalCwF modes where
  Con := fun _ => Type
  Sub := fun source target => source -> target
  sid := fun _ value => value
  scomp := fun earlier later value => later (earlier value)
  Ty := fun _ => Type
  Tm := fun context type => context -> type
  tySub := fun type _ => type
  tmSub := fun term substitution value => term (substitution value)
  tySub_id := fun _ => rfl
  tySub_comp := fun _ _ _ => rfl
  empty := fun _ => PUnit
  ext := fun context type => context × type
  wk := fun _ pair => pair.1
  vz := fun _ pair => pair.2
  sext := fun substitution term value =>
    (substitution value, term value)
  pi := fun domain codomain => domain -> codomain
  univ := fun _ => PUnit
  el := fun _ => PUnit
  lock := fun _ context => context
  boxTy := by
    intro high low modality context type
    exact type

def laws : ModalCwFLaws modes cwf where
  scomp_sid_left := fun _ => rfl
  scomp_sid_right := fun _ => rfl
  scomp_assoc := fun _ _ _ => rfl
  tmSub_id := fun _ => HEq.rfl
  tmSub_comp := fun _ _ _ => HEq.rfl
  wk_sext := fun _ _ => rfl
  vz_sext := fun _ _ => HEq.rfl
  sext_eta := fun _ => rfl
  piLaws :=
    { lam := fun body context argument => body (context, argument)
      app := fun function argument context => function context (argument context)
      beta := fun _ _ => rfl
      pi_sub := fun _ _ _ => rfl
      extensional := by
        intro mode context domain codomain left right pointwise
        funext contextPoint
        funext argument
        have functionsAgree := pointwise
          (Δ := PUnit)
          (fun _ => contextPoint)
          (fun _ => argument)
        exact congrFun (eq_of_heq functionsAgree) PUnit.unit }
  lockSub := by
    intro high low modality first last substitution
    exact substitution
  lockSub_sid := by intros; rfl
  lockSub_comp := by intros; rfl
  boxTy_natural := by intros; rfl
  lock_id := by intros; rfl
  lock_comp := by intros; rfl
  lockSub_id := by intros; exact HEq.rfl
  lockSub_modal_comp := by intros; exact HEq.rfl
  boxTy_id := by
    intro mode context type
    simp [cwf]
  boxTy_comp := by
    intro first middle last earlier later context direct nested sameType
    simpa [cwf] using sameType

def selected : WideSubtheory modes := WideSubtheory.all modes

def quotation :
    SelectedQuotationTermStructure modes cwf laws selected where
  introduce := by
    intro high low modality admitted context type term
    exact term
  introduce_sub := by intros; simp [cwf, laws]
  introduce_id := by intros; simp [cwf]

def splicing : SelectedSpliceTermStructure modes cwf laws selected where
  splice := by
    intro high low modality admitted context type code
    exact code
  splice_sub := by
    intros
    simp [cwf, laws, ModalCwF.castTm]
  splice_id := by intros; simp [cwf]

def beta :
    SelectedQuoteSpliceBeta modes cwf laws selected quotation splicing where
  splice_quote := by intros; simp [quotation, splicing]

def eta :
    SelectedQuoteSpliceEta modes cwf laws selected quotation splicing where
  quote_splice := by intros; simp [quotation, splicing]

/-- Quotation, substitution-stable splicing, beta, and eta coexist over
arbitrary small function spaces in the identity-modal control. -/
theorem quote_splice_exact_control :
    Nonempty
        (SelectedQuoteSpliceBeta modes cwf laws selected quotation splicing) /\
      Nonempty
        (SelectedQuoteSpliceEta modes cwf laws selected quotation splicing) :=
  ⟨⟨beta⟩, ⟨eta⟩⟩

/-- The induced Boolean code/body comparison is globally information
preserving in the exact identity-modal control. -/
theorem bool_comparison_not_loses :
    ¬ (Mettapedia.Computability.SplitReadoutComparison.comparison
      (beta.readout (high := PUnit.unit) (low := PUnit.unit)
        PUnit.unit trivial
        (context := PUnit) (type := Bool))).LosesProgramInformation := by
  rw [Mettapedia.Computability.SplitReadoutComparison.not_loses_iff_faithful]
  rw [beta.faithful_iff_quote_splice
    (high := PUnit.unit) (low := PUnit.unit) PUnit.unit trivial]
  exact eta.quote_splice
    (high := PUnit.unit) (low := PUnit.unit) PUnit.unit trivial

end FunctionModel

/-! ## Fibre-level independence and information-loss controls -/

namespace FibreCanary

/-- Quotation can exist when splicing is impossible. -/
theorem quotation_does_not_imply_splicing :
    Nonempty (Empty -> PUnit) /\
      ¬ Nonempty (PUnit -> Empty) := by
  constructor
  · exact ⟨fun impossible => impossible.elim⟩
  · rintro ⟨splice⟩
    exact (splice PUnit.unit).elim

/-- A constant code token cannot support beta-correct execution of two
distinct bodies.  Any executable quotation must retain enough information to
be injective on the bodies it promises to reconstruct. -/
theorem constant_token_quotation_has_no_beta_splice :
    ¬ exists splice : PUnit -> Bool,
      forall body : Bool, splice PUnit.unit = body := by
  rintro ⟨splice, beta⟩
  exact Bool.false_ne_true ((beta false).symm.trans (beta true))

/-- Code may retain one intensional tag in addition to its splice body. -/
def taggedReadout (Body : Type u) : SplitReadout (Body × Bool) Body where
  observe := Prod.fst
  representative := fun body => (body, false)
  observe_representative := fun _ => rfl

/-- Beta holds for the tagged code interface. -/
theorem tagged_beta {Body : Type u} (body : Body) :
    (taggedReadout Body).observe ((taggedReadout Body).representative body) =
      body :=
  rfl

/-- Eta fails: quotation selects the canonical false tag and cannot
reconstruct an independently retained true tag. -/
theorem tagged_not_eta {Body : Type u} (body : Body) :
    (taggedReadout Body).representative
        ((taggedReadout Body).observe (body, true)) ≠
      (body, true) := by
  intro equality
  exact Bool.false_ne_true (congrArg (fun pair => pair.2) equality)

/-- The retained tag prevents a globally exact computational-trinity bridge. -/
theorem tagged_comparison_loses {Body : Type u} (body : Body) :
    (Mettapedia.Computability.SplitReadoutComparison.comparison
      (taggedReadout Body)).LosesProgramInformation := by
  let context :=
    Opposite.op
      (Discrete.mk PUnit.unit :
        Mettapedia.Computability.SplitReadoutComparison.Context)
  exact ⟨context, (body, false), (body, true), by
    intro equality
    exact Bool.false_ne_true (congrArg Prod.snd equality), rfl⟩

/-- The visible body observation factors through splicing. -/
theorem tagged_body_factors {Body : Type u} :
    (taggedReadout Body).FactorsObserver Prod.fst := by
  exact ⟨fun body => body, fun _ => rfl⟩

/-- The retained tag observation does not factor through splicing. -/
theorem tagged_tag_does_not_factor {Body : Type u} (body : Body) :
    ¬ (taggedReadout Body).FactorsObserver Prod.snd := by
  rw [(taggedReadout Body).factorsObserver_iff_fibreInvariant]
  intro invariant
  have tagsEqual := invariant
    (left := (body, false)) (right := (body, true)) rfl
  exact Bool.false_ne_true tagsEqual

/-- Despite global information loss, canonical quotations retain the exact
fragment supplied by every split readout. -/
def tagged_canonical_exact (Body : Type u) :=
  Mettapedia.Computability.SplitReadoutComparison.canonicalExactComparison
    (taggedReadout Body)

end FibreCanary

#print axioms ContextualObject.instantiate_identity
#print axioms ContextualObject.instantiate_comp
#print axioms ContextualObject.instantiate_freshen_inverse
#print axioms ContextualObject.FamiliesCanary.ambient_stops_explicit_instantiation_enters
#print axioms SelectedQuoteSpliceBeta.quotation_injective
#print axioms SelectedQuoteSpliceBeta.splicing_surjective
#print axioms SelectedQuoteSpliceBeta.codeBodyEquiv
#print axioms SelectedQuoteSpliceBeta.faithful_iff_quote_splice
#print axioms SelectedQuoteSpliceBeta.comparison_not_loses_iff_quote_splice
#print axioms SelectedQuoteSpliceBeta.observer_factors_through_splice_iff_fibreInvariant
#print axioms SelectedQuoteSpliceBeta.identity_observer_factors_iff_quote_splice
#print axioms SelectedQuoteSpliceEta.splicing_injective
#print axioms SelectedQuoteSpliceEta.quotation_surjective
#print axioms FunctionModel.quote_splice_exact_control
#print axioms FunctionModel.bool_comparison_not_loses
#print axioms FibreCanary.quotation_does_not_imply_splicing
#print axioms FibreCanary.constant_token_quotation_has_no_beta_splice
#print axioms FibreCanary.tagged_not_eta
#print axioms FibreCanary.tagged_comparison_loses
#print axioms FibreCanary.tagged_body_factors
#print axioms FibreCanary.tagged_tag_does_not_factor

end Mettapedia.TypeTheory.ContextualCode
