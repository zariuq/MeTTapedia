/-!
# Multimodal categories with families

This module isolates the general categorical syntax used by staged and
reflective dependent type theories.  It is independent of MeTTa syntax,
runtime patterns, and any particular universe presentation.

A `ModeTheory` is a small strict category of modalities.  A `ModalCwF` carries
contexts, substitutions, types, terms, comprehension, dependent products, a
Tarski universe, and Fitch-style locking over those modes.  `ModalCwFLaws`
records the equational layer, while term-level quotation is deliberately
separate additional structure.

The separation matters: a bare modal CwF determines how contexts and types
move along modalities, but it does not determine a quotation operation on
terms.  Concrete languages must earn that enrichment explicitly.
-/

namespace Mettapedia.TypeTheory

/-! ## Mode theories and cost grading -/

/-- A small strict category of modes: the modality parameter of the spine. -/
structure ModeTheory where
  Mode : Type
  Hom : Mode → Mode → Type
  id : (mode : Mode) → Hom mode mode
  comp : {first middle last : Mode} →
    Hom first middle → Hom middle last → Hom first last
  id_comp : ∀ {first last : Mode} (morphism : Hom first last),
    comp (id first) morphism = morphism
  comp_id : ∀ {first last : Mode} (morphism : Hom first last),
    comp morphism (id last) = morphism
  comp_assoc : ∀ {first second third last : Mode}
    (earlier : Hom first second) (middle : Hom second third)
    (later : Hom third last),
    comp (comp earlier middle) later = comp earlier (comp middle later)

/-- Cost grading over a mode theory: modalities carry grades in a monoid and
composition accumulates them.  Commutativity is not required because
sequential resource use need not commute. -/
structure CostGrading (modes : ModeTheory) where
  Grade : Type
  unit : Grade
  add : Grade → Grade → Grade
  add_assoc : ∀ first second third,
    add (add first second) third = add first (add second third)
  unit_add : ∀ grade, add unit grade = grade
  add_unit : ∀ grade, add grade unit = grade
  gradeOf : {first last : modes.Mode} → modes.Hom first last → Grade
  gradeOf_id : ∀ mode, gradeOf (modes.id mode) = unit
  gradeOf_comp : ∀ {first middle last : modes.Mode}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last),
    gradeOf (modes.comp earlier later) = add (gradeOf earlier) (gradeOf later)

/-! ## The contextual multimodal CwF spine -/

/-- Contexts, substitutions, dependent types and terms, comprehension,
dependent products, a Tarski universe, and modal locking over a mode theory. -/
structure ModalCwF (modes : ModeTheory) where
  /-- Contexts may contain small Lean types, so the context collection lives
  one universe above the mode theory. -/
  Con : modes.Mode → Type 1
  /-- Individual substitutions remain small. -/
  Sub : {mode : modes.Mode} → Con mode → Con mode → Type
  sid : {mode : modes.Mode} → (context : Con mode) → Sub context context
  scomp : {mode : modes.Mode} → {first middle last : Con mode} →
    Sub first middle → Sub middle last → Sub first last
  Ty : {mode : modes.Mode} → Con mode → Type 1
  /-- Each code in the large collection `Ty context` decodes to a small term
  carrier. -/
  Tm : {mode : modes.Mode} → (context : Con mode) → Ty context → Type
  tySub : {mode : modes.Mode} → {first last : Con mode} →
    Ty last → Sub first last → Ty first
  tmSub : {mode : modes.Mode} → {first last : Con mode} →
    {type : Ty last} → Tm last type →
    (substitution : Sub first last) → Tm first (tySub type substitution)
  tySub_id : ∀ {mode : modes.Mode} {context : Con mode}
    (type : Ty context), tySub type (sid context) = type
  tySub_comp : ∀ {mode : modes.Mode} {first middle last : Con mode}
    (type : Ty last) (earlier : Sub first middle) (later : Sub middle last),
    tySub type (scomp earlier later) = tySub (tySub type later) earlier
  empty : (mode : modes.Mode) → Con mode
  ext : {mode : modes.Mode} → (context : Con mode) → Ty context → Con mode
  wk : {mode : modes.Mode} → {context : Con mode} →
    (type : Ty context) → Sub (ext context type) context
  vz : {mode : modes.Mode} → {context : Con mode} →
    (type : Ty context) → Tm (ext context type) (tySub type (wk type))
  sext : {mode : modes.Mode} → {first last : Con mode} →
    {type : Ty last} → (substitution : Sub first last) →
    Tm first (tySub type substitution) → Sub first (ext last type)
  pi : {mode : modes.Mode} → {context : Con mode} →
    (domain : Ty context) → Ty (ext context domain) → Ty context
  univ : {mode : modes.Mode} → (context : Con mode) → Ty context
  el : {mode : modes.Mode} → {context : Con mode} →
    Tm context (univ context) → Ty context
  lock : {high low : modes.Mode} → modes.Hom high low → Con low → Con high
  boxTy : {high low : modes.Mode} → (modality : modes.Hom high low) →
    {context : Con low} → Ty (lock modality context) → Ty context

namespace ModalCwF

/-- Transport a term along equality of its type code. -/
def castTm {modes : ModeTheory} (cwf : ModalCwF modes)
    {mode : modes.Mode} {context : cwf.Con mode}
    {source target : cwf.Ty context}
    (equalTypes : source = target) (term : cwf.Tm context source) :
    cwf.Tm context target :=
  equalTypes ▸ term

/-- Lift a substitution through context comprehension.  The only transport
is the already-required type-substitution composition law. -/
def liftSub {modes : ModeTheory} (cwf : ModalCwF modes)
    {mode : modes.Mode} {first last : cwf.Con mode}
    {type : cwf.Ty last} (substitution : cwf.Sub first last) :
    cwf.Sub (cwf.ext first (cwf.tySub type substitution))
      (cwf.ext last type) :=
  cwf.sext
    (cwf.scomp (cwf.wk (cwf.tySub type substitution)) substitution)
    (cwf.castTm
      (cwf.tySub_comp type (cwf.wk (cwf.tySub type substitution))
        substitution).symm
      (cwf.vz (cwf.tySub type substitution)))

/-- Pair the identity substitution with a term, inserting only the required
transport along `tySub_id`. -/
def selfExtend {modes : ModeTheory} (cwf : ModalCwF modes)
    {mode : modes.Mode} {context : cwf.Con mode} {type : cwf.Ty context}
    (term : cwf.Tm context type) : cwf.Sub context (cwf.ext context type) :=
  cwf.sext (cwf.sid context) (cwf.castTm (cwf.tySub_id type).symm term)

/-- Replace only the designated empty context.  This operation is useful for
separating the raw contextual operations from the terminality law imposed by
semantic CwF coherence. -/
def replaceEmpty {modes : ModeTheory} (cwf : ModalCwF modes)
    (replacement : (mode : modes.Mode) → cwf.Con mode) : ModalCwF modes :=
  { cwf with empty := replacement }

@[simp] theorem replaceEmpty_empty {modes : ModeTheory} (cwf : ModalCwF modes)
    (replacement : (mode : modes.Mode) → cwf.Con mode)
    (mode : modes.Mode) :
    (cwf.replaceEmpty replacement).empty mode = replacement mode :=
  rfl

end ModalCwF

/-- Introduction, elimination, beta, substitution stability, and generalized
eta/extensionality for dependent products.  Generalized elements keep the eta
law meaningful even when a context has no global sections. -/
structure PiStructure (modes : ModeTheory) (cwf : ModalCwF modes) where
  lam : {mode : modes.Mode} → {context : cwf.Con mode} →
    {domain : cwf.Ty context} → {codomain : cwf.Ty (cwf.ext context domain)} →
    cwf.Tm (cwf.ext context domain) codomain →
      cwf.Tm context (cwf.pi domain codomain)
  app : {mode : modes.Mode} → {context : cwf.Con mode} →
    {domain : cwf.Ty context} → {codomain : cwf.Ty (cwf.ext context domain)} →
    cwf.Tm context (cwf.pi domain codomain) →
    (argument : cwf.Tm context domain) →
      cwf.Tm context (cwf.tySub codomain (cwf.selfExtend argument))
  beta : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    {domain : cwf.Ty context} {codomain : cwf.Ty (cwf.ext context domain)}
    (body : cwf.Tm (cwf.ext context domain) codomain)
    (argument : cwf.Tm context domain),
    app (lam body) argument = cwf.tmSub body (cwf.selfExtend argument)
  pi_sub : ∀ {mode : modes.Mode} {first last : cwf.Con mode}
    (domain : cwf.Ty last) (codomain : cwf.Ty (cwf.ext last domain))
    (substitution : cwf.Sub first last),
    cwf.tySub (cwf.pi domain codomain) substitution =
      cwf.pi (cwf.tySub domain substitution)
        (cwf.tySub codomain (cwf.liftSub substitution))
  extensional : ∀ {mode : modes.Mode} {Γ : cwf.Con mode}
    {A : cwf.Ty Γ} {B : cwf.Ty (cwf.ext Γ A)}
    (left right : cwf.Tm Γ (cwf.pi A B)),
    (∀ {Δ : cwf.Con mode} (σ : cwf.Sub Δ Γ)
      (argument : cwf.Tm Δ (cwf.tySub A σ)),
      HEq
        (app
          (cwf.castTm (pi_sub A B σ)
            (cwf.tmSub left σ)) argument)
        (app
          (cwf.castTm (pi_sub A B σ)
            (cwf.tmSub right σ)) argument)) →
    left = right

namespace PiStructure

/-- Dependent-product structure is invariant under changing only the
designated empty context. -/
def replaceEmpty {modes : ModeTheory} {cwf : ModalCwF modes}
    (products : PiStructure modes cwf)
    (replacement : (mode : modes.Mode) → cwf.Con mode) :
    PiStructure modes (cwf.replaceEmpty replacement) where
  lam := products.lam
  app := products.app
  beta := products.beta
  pi_sub := products.pi_sub
  extensional := products.extensional

end PiStructure

/-- The complete equational layer over a `ModalCwF`.  `HEq` appears only
where an equation itself identifies dependent fibres. -/
structure ModalCwFLaws (modes : ModeTheory) (cwf : ModalCwF modes) where
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
  piLaws : PiStructure modes cwf
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

namespace ModalCwFLaws

/-- The basic CwF and modal equations are invariant under replacing the
designated empty context.  Terminality is therefore an independent semantic
law, not a consequence smuggled into the operational record. -/
def replaceEmpty {modes : ModeTheory} {cwf : ModalCwF modes}
    (laws : ModalCwFLaws modes cwf)
    (replacement : (mode : modes.Mode) → cwf.Con mode) :
    ModalCwFLaws modes (cwf.replaceEmpty replacement) where
  scomp_sid_left := laws.scomp_sid_left
  scomp_sid_right := laws.scomp_sid_right
  scomp_assoc := laws.scomp_assoc
  tmSub_id := laws.tmSub_id
  tmSub_comp := laws.tmSub_comp
  wk_sext := laws.wk_sext
  vz_sext := laws.vz_sext
  sext_eta := laws.sext_eta
  piLaws := laws.piLaws.replaceEmpty replacement
  lockSub := laws.lockSub
  lockSub_sid := laws.lockSub_sid
  lockSub_comp := laws.lockSub_comp
  boxTy_natural := laws.boxTy_natural
  lock_id := laws.lock_id
  lock_comp := laws.lock_comp
  lockSub_id := laws.lockSub_id
  lockSub_modal_comp := laws.lockSub_modal_comp
  boxTy_id := laws.boxTy_id
  boxTy_comp := laws.boxTy_comp

end ModalCwFLaws

/-! ## Semantic CwF coherence

The operational spine and its equations do not by themselves state the
universal property of the empty context, naturality of comprehension, or
stability of Tarski decoding.  These are kept in a separate extension so a
partial presentation can use `ModalCwFLaws` without silently claiming the
stronger semantic structure. -/

/-- The universal and universe-coherence laws that turn the contextual spine
into a semantic modal CwF with a substitution-stable Tarski universe. -/
structure ModalCwFCoherence (modes : ModeTheory) (cwf : ModalCwF modes)
    (laws : ModalCwFLaws modes cwf) where
  /-- The designated empty context is terminal at every mode. -/
  empty_sub_unique : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    (left right : cwf.Sub context (cwf.empty mode)), left = right
  /-- Pairing into comprehension commutes with precomposition. -/
  sext_natural : ∀ {mode : modes.Mode}
    {source middle target : cwf.Con mode} {type : cwf.Ty target}
    (earlier : cwf.Sub source middle) (later : cwf.Sub middle target)
    (term : cwf.Tm middle (cwf.tySub type later)),
    cwf.scomp earlier (cwf.sext later term) =
      cwf.sext (cwf.scomp earlier later)
        (cwf.castTm (cwf.tySub_comp type earlier later).symm
          (cwf.tmSub term earlier))
  /-- The Tarski universe is stable under substitution. -/
  univ_natural : ∀ {mode : modes.Mode}
    {source target : cwf.Con mode} (substitution : cwf.Sub source target),
    cwf.tySub (cwf.univ target) substitution = cwf.univ source
  /-- Decoding a reindexed code agrees with reindexing its decoded type. -/
  el_natural : ∀ {mode : modes.Mode}
    {source target : cwf.Con mode}
    (code : cwf.Tm target (cwf.univ target))
    (substitution : cwf.Sub source target),
    cwf.el
        (cwf.castTm (univ_natural substitution)
          (cwf.tmSub code substitution)) =
      cwf.tySub (cwf.el code) substitution

namespace ModalCwFCoherence

/-- The general comprehension eta law follows from identity eta and
naturality: a substitution into an extended context is uniquely its base
projection paired with its final component. -/
theorem sext_unique {modes : ModeTheory} {cwf : ModalCwF modes}
    {laws : ModalCwFLaws modes cwf}
    (coherence : ModalCwFCoherence modes cwf laws)
    {mode : modes.Mode} {source target : cwf.Con mode}
    (type : cwf.Ty target) (substitution : cwf.Sub source (cwf.ext target type)) :
    substitution =
      cwf.sext (cwf.scomp substitution (cwf.wk type))
        (cwf.castTm
          (cwf.tySub_comp type substitution (cwf.wk type)).symm
          (cwf.tmSub (cwf.vz type) substitution)) := by
  calc
    substitution =
        cwf.scomp substitution (cwf.sid (cwf.ext target type)) :=
      (laws.scomp_sid_right substitution).symm
    _ = cwf.scomp substitution
        (cwf.sext (cwf.wk type) (cwf.vz type)) := by
      rw [laws.sext_eta type]
    _ = cwf.sext (cwf.scomp substitution (cwf.wk type))
        (cwf.castTm
          (cwf.tySub_comp type substitution (cwf.wk type)).symm
          (cwf.tmSub (cwf.vz type) substitution)) :=
      coherence.sext_natural substitution (cwf.wk type) (cwf.vz type)

end ModalCwFCoherence

/-! ## Term-level quotation as additional modal structure -/

/-- Term introduction for modal types, stable under ordinary substitution and
identity modalities.  No idempotence or multiplication law is assumed:
successive quotation may retain genuinely distinct staging information. -/
structure QuotationTermStructure (modes : ModeTheory)
    (cwf : ModalCwF modes) (laws : ModalCwFLaws modes cwf) where
  quoteTm : {high low : modes.Mode} → (modality : modes.Hom high low) →
    {context : cwf.Con low} → {type : cwf.Ty (cwf.lock modality context)} →
    cwf.Tm (cwf.lock modality context) type →
      cwf.Tm context (cwf.boxTy modality type)
  quote_sub : ∀ {high low : modes.Mode}
    (modality : modes.Hom high low) {first last : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality last)}
    (term : cwf.Tm (cwf.lock modality last) type)
    (substitution : cwf.Sub first last),
    HEq
      (cwf.tmSub (quoteTm modality term) substitution)
      (quoteTm modality
        (cwf.tmSub term (laws.lockSub modality substitution)))
  quote_id : ∀ {mode : modes.Mode} {context : cwf.Con mode}
    {type : cwf.Ty (cwf.lock (modes.id mode) context)}
    (term : cwf.Tm (cwf.lock (modes.id mode) context) type),
    HEq (quoteTm (modes.id mode) term) term

end Mettapedia.TypeTheory
