import Mettapedia.TypeTheory.DependentProductCapabilities
import Mathlib.Logic.Equiv.Basic

/-!
# Independent law capabilities of a modal CwF

The data decomposition in `ContextualModalCapabilities` separates formation
operations.  This module performs the corresponding separation for laws.

The historical `ModalCwFLaws` record contains contextual substitution laws,
beta-dependent products, generalized function extensionality, and modal-locking
laws.  `IntensionalModalCwFLaws` removes only generalized function
extensionality.  The old record is exactly equivalent to an intensional law
bundle plus an explicitly supplied extensionality capability.

Semantic coherence is split a second time: terminal/comprehension coherence
and Tarski-universe substitution laws are independent records.  This avoids
making a selected universe part of the meaning of contextual structure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualModalLawCapabilities

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.DependentProductCapabilities

/-- Category and comprehension equations for the contextual core of a
`ModalCwF`.  Products, universes, modalities, and quotation are absent. -/
structure ContextualSubstitutionLaws (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  scomp_sid_left : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    (substitution : cwf.Sub first last),
    cwf.scomp (cwf.sid first) substitution = substitution
  scomp_sid_right : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    (substitution : cwf.Sub first last),
    cwf.scomp substitution (cwf.sid last) = substitution
  scomp_assoc : ∀ {mode : modes.Mode}
    {first second third last : cwf.Con mode}
    (earlier : cwf.Sub first second) (middle : cwf.Sub second third)
    (later : cwf.Sub third last),
    cwf.scomp (cwf.scomp earlier middle) later =
      cwf.scomp earlier (cwf.scomp middle later)
  tmSub_id : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    {type : cwf.Ty context} (term : cwf.Tm context type),
    HEq (cwf.tmSub term (cwf.sid context)) term
  tmSub_comp : ∀ {mode : modes.Mode}
    {first middle last : cwf.Con mode} {type : cwf.Ty last}
    (term : cwf.Tm last type) (earlier : cwf.Sub first middle)
    (later : cwf.Sub middle last),
    HEq (cwf.tmSub term (cwf.scomp earlier later))
      (cwf.tmSub (cwf.tmSub term later) earlier)
  wk_sext : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    {type : cwf.Ty last} (substitution : cwf.Sub first last)
    (term : cwf.Tm first (cwf.tySub type substitution)),
    cwf.scomp (cwf.sext substitution term) (cwf.wk type) = substitution
  vz_sext : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    {type : cwf.Ty last} (substitution : cwf.Sub first last)
    (term : cwf.Tm first (cwf.tySub type substitution)),
    HEq (cwf.tmSub (cwf.vz type) (cwf.sext substitution term)) term
  sext_eta : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    (type : cwf.Ty context),
    cwf.sext (cwf.wk type) (cwf.vz type) = cwf.sid (cwf.ext context type)

/-- Substitution and composition laws for modal context locking and modal
types.  Term quotation is a separate capability. -/
structure ModalLockingLaws (modes : ModeTheory) (cwf : ModalCwF modes) where
  lockSub : {high low : modes.Mode} → (modality : modes.Hom high low) →
    {first last : cwf.Con low} → cwf.Sub first last →
      cwf.Sub (cwf.lock modality first) (cwf.lock modality last)
  lockSub_sid : ∀ {high low : modes.Mode}
    (modality : modes.Hom high low) (context : cwf.Con low),
    lockSub modality (cwf.sid context) = cwf.sid (cwf.lock modality context)
  lockSub_comp : ∀ {high low : modes.Mode}
    (modality : modes.Hom high low) {first middle last : cwf.Con low}
    (earlier : cwf.Sub first middle) (later : cwf.Sub middle last),
    lockSub modality (cwf.scomp earlier later) =
      cwf.scomp (lockSub modality earlier) (lockSub modality later)
  boxTy_natural : ∀ {high low : modes.Mode}
    (modality : modes.Hom high low) {first last : cwf.Con low}
    (type : cwf.Ty (cwf.lock modality last))
    (substitution : cwf.Sub first last),
    cwf.tySub (cwf.boxTy modality type) substitution =
      cwf.boxTy modality (cwf.tySub type (lockSub modality substitution))
  lock_id : ∀ {mode : modes.Mode} (context : cwf.Con mode),
    cwf.lock (modes.id mode) context = context
  lock_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last)
    (context : cwf.Con last),
    cwf.lock (modes.comp earlier later) context =
      cwf.lock earlier (cwf.lock later context)
  lockSub_id : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    (substitution : cwf.Sub first last),
    HEq (lockSub (modes.id mode) substitution) substitution
  lockSub_modal_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last)
    {source target : cwf.Con last} (substitution : cwf.Sub source target),
    HEq (lockSub (modes.comp earlier later) substitution)
      (lockSub earlier (lockSub later substitution))
  boxTy_id : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    (type : cwf.Ty (cwf.lock (modes.id mode) context)),
    HEq (cwf.boxTy (modes.id mode) type) type
  boxTy_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last)
    {context : cwf.Con last}
    (direct : cwf.Ty (cwf.lock (modes.comp earlier later) context))
    (nested : cwf.Ty (cwf.lock earlier (cwf.lock later context))),
    HEq direct nested →
      HEq (cwf.boxTy (modes.comp earlier later) direct)
        (cwf.boxTy later (cwf.boxTy earlier nested))

/-- Contextual and modal laws with beta-dependent products, but without
generalized function extensionality. -/
structure IntensionalModalCwFLaws (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  contextual : ContextualSubstitutionLaws modes cwf
  products : PiBetaStructure modes cwf
  locking : ModalLockingLaws modes cwf

namespace ModalCwFLaws

/-- Forget generalized function extensionality while retaining every other
law in the historical record. -/
def toIntensional {modes : ModeTheory} {cwf : ModalCwF modes}
    (laws : Mettapedia.TypeTheory.ModalCwFLaws modes cwf) :
    IntensionalModalCwFLaws modes cwf where
  contextual :=
    { scomp_sid_left := laws.scomp_sid_left
      scomp_sid_right := laws.scomp_sid_right
      scomp_assoc := laws.scomp_assoc
      tmSub_id := laws.tmSub_id
      tmSub_comp := laws.tmSub_comp
      wk_sext := laws.wk_sext
      vz_sext := laws.vz_sext
      sext_eta := laws.sext_eta }
  products :=
    DependentProductCapabilities.PiStructure.toBeta laws.piLaws
  locking :=
    { lockSub := laws.lockSub
      lockSub_sid := laws.lockSub_sid
      lockSub_comp := laws.lockSub_comp
      boxTy_natural := laws.boxTy_natural
      lock_id := laws.lock_id
      lock_comp := laws.lock_comp
      lockSub_id := laws.lockSub_id
      lockSub_modal_comp := laws.lockSub_modal_comp
      boxTy_id := laws.boxTy_id
      boxTy_comp := laws.boxTy_comp }

/-- Extract the independent generalized function-extensionality capability. -/
def toProductExtensionality {modes : ModeTheory} {cwf : ModalCwF modes}
    (laws : Mettapedia.TypeTheory.ModalCwFLaws modes cwf) :
    PiApplicationExtensionality modes cwf (toIntensional laws).products :=
  DependentProductCapabilities.PiStructure.toApplicationExtensionality
    laws.piLaws

end ModalCwFLaws

namespace IntensionalModalCwFLaws

/-- Restore the historical law bundle after generalized function
extensionality has been supplied explicitly. -/
def withProductExtensionality {modes : ModeTheory} {cwf : ModalCwF modes}
    (laws : IntensionalModalCwFLaws modes cwf)
    (extensionality : PiApplicationExtensionality modes cwf laws.products) :
    Mettapedia.TypeTheory.ModalCwFLaws modes cwf where
  scomp_sid_left := laws.contextual.scomp_sid_left
  scomp_sid_right := laws.contextual.scomp_sid_right
  scomp_assoc := laws.contextual.scomp_assoc
  tmSub_id := laws.contextual.tmSub_id
  tmSub_comp := laws.contextual.tmSub_comp
  wk_sext := laws.contextual.wk_sext
  vz_sext := laws.contextual.vz_sext
  sext_eta := laws.contextual.sext_eta
  piLaws := laws.products.withApplicationExtensionality extensionality
  lockSub := laws.locking.lockSub
  lockSub_sid := laws.locking.lockSub_sid
  lockSub_comp := laws.locking.lockSub_comp
  boxTy_natural := laws.locking.boxTy_natural
  lock_id := laws.locking.lock_id
  lock_comp := laws.locking.lock_comp
  lockSub_id := laws.locking.lockSub_id
  lockSub_modal_comp := laws.locking.lockSub_modal_comp
  boxTy_id := laws.locking.boxTy_id
  boxTy_comp := laws.locking.boxTy_comp

end IntensionalModalCwFLaws

/-- The law-level decomposition of the historical extensional bundle. -/
structure ModalCwFLawDecomposition (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  intensional : IntensionalModalCwFLaws modes cwf
  productExtensionality :
    PiApplicationExtensionality modes cwf intensional.products

/-- The historical law record is exactly the intensional laws plus one
explicit function-extensionality capability. -/
def modalCwFLawDecompositionEquiv (modes : ModeTheory) (cwf : ModalCwF modes) :
    Mettapedia.TypeTheory.ModalCwFLaws modes cwf ≃
      ModalCwFLawDecomposition modes cwf where
  toFun laws :=
    { intensional := ModalCwFLaws.toIntensional laws
      productExtensionality := ModalCwFLaws.toProductExtensionality laws }
  invFun decomposition :=
    decomposition.intensional.withProductExtensionality
      decomposition.productExtensionality
  left_inv := by
    intro laws
    cases laws
    rfl
  right_inv := by
    intro decomposition
    cases decomposition with
    | mk intensional extensionality =>
        cases intensional with
        | mk contextual products locking =>
            cases contextual
            cases products
            cases locking
            cases extensionality
            rfl

/-! ## Semantic coherence capabilities -/

/-- Terminality and naturality of context comprehension. -/
structure ContextualSemanticCoherence (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  empty_sub_unique : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    (left right : cwf.Sub context (cwf.empty mode)), left = right
  sext_natural : ∀ {mode : modes.Mode}
    {source middle target : cwf.Con mode} {type : cwf.Ty target}
    (earlier : cwf.Sub source middle) (later : cwf.Sub middle target)
    (term : cwf.Tm middle (cwf.tySub type later)),
    cwf.scomp earlier (cwf.sext later term) =
      cwf.sext (cwf.scomp earlier later)
        (cwf.castTm (cwf.tySub_comp type earlier later).symm
          (cwf.tmSub term earlier))

/-- Substitution stability of one selected Tarski universe and its decoding
operation. -/
structure TarskiUniverseSubstitutionLaws (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  univ_natural : ∀ {mode : modes.Mode}
    {source target : cwf.Con mode} (substitution : cwf.Sub source target),
    cwf.tySub (cwf.univ target) substitution = cwf.univ source
  el_natural : ∀ {mode : modes.Mode}
    {source target : cwf.Con mode}
    (code : cwf.Tm target (cwf.univ target))
    (substitution : cwf.Sub source target),
    cwf.el
        (cwf.castTm (univ_natural substitution)
          (cwf.tmSub code substitution)) =
      cwf.tySub (cwf.el code) substitution

/-- The semantic-coherence decomposition of the historical record. -/
structure ModalCwFCoherenceDecomposition (modes : ModeTheory)
    (cwf : ModalCwF modes) where
  contextual : ContextualSemanticCoherence modes cwf
  tarski : TarskiUniverseSubstitutionLaws modes cwf

namespace ModalCwFCoherence

def decompose {modes : ModeTheory} {cwf : ModalCwF modes}
    {laws : Mettapedia.TypeTheory.ModalCwFLaws modes cwf}
    (coherence : Mettapedia.TypeTheory.ModalCwFCoherence modes cwf laws) :
    ModalCwFCoherenceDecomposition modes cwf where
  contextual :=
    { empty_sub_unique := coherence.empty_sub_unique
      sext_natural := coherence.sext_natural }
  tarski :=
    { univ_natural := coherence.univ_natural
      el_natural := coherence.el_natural }

end ModalCwFCoherence

namespace ModalCwFCoherenceDecomposition

def assemble {modes : ModeTheory} {cwf : ModalCwF modes}
    (laws : Mettapedia.TypeTheory.ModalCwFLaws modes cwf)
    (coherence : ModalCwFCoherenceDecomposition modes cwf) :
    Mettapedia.TypeTheory.ModalCwFCoherence modes cwf laws where
  empty_sub_unique := coherence.contextual.empty_sub_unique
  sext_natural := coherence.contextual.sext_natural
  univ_natural := coherence.tarski.univ_natural
  el_natural := coherence.tarski.el_natural

end ModalCwFCoherenceDecomposition

/-- The old coherence record is exactly contextual semantic coherence plus
the selected universe's substitution laws. -/
def modalCwFCoherenceDecompositionEquiv
    (modes : ModeTheory) (cwf : ModalCwF modes)
    (laws : Mettapedia.TypeTheory.ModalCwFLaws modes cwf) :
    Mettapedia.TypeTheory.ModalCwFCoherence modes cwf laws ≃
      ModalCwFCoherenceDecomposition modes cwf where
  toFun := ModalCwFCoherence.decompose
  invFun := ModalCwFCoherenceDecomposition.assemble laws
  left_inv := by
    intro coherence
    cases coherence
    rfl
  right_inv := by
    intro decomposition
    cases decomposition with
    | mk contextual tarski =>
        cases contextual
        cases tarski
        rfl

#print axioms ModalCwFLaws.toIntensional
#print axioms IntensionalModalCwFLaws.withProductExtensionality
#print axioms modalCwFLawDecompositionEquiv
#print axioms modalCwFCoherenceDecompositionEquiv

end Mettapedia.TypeTheory.ContextualModalLawCapabilities
