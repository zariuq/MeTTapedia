import Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary

/-!
# Portable simultaneous substitution for TH0

The TH0 interchange boundary already provides a canonical typed term packet
and a fail-closed decoder into the intrinsic HOL syntax.  This module exposes
simultaneous substitution as a separate, portable algorithmic service over
that packet.

The service is deliberately smaller than higher-order unification or
superposition.  It accepts an ordered image for every variable in a declared
source context, checks every image in one declared target context, applies the
existing capture-avoiding intrinsic substitution, and re-encodes the result.
No search or logic-specific inference is hidden in the operation.

Contexts and ordered images are included in the canonical wire packet so the
same request can be carried by different MeTTa dialects or lowered to a native
implementation.  Successful outputs reflect to intrinsic substitution;
ill-scoped, ill-typed, length-mismatched, and context-incompatible requests
fail closed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService

open Mettapedia.Logic.HOL
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary
open Mettapedia.TypeTheory.AuthorityTheory

/-! ## Ordered substitution images -/

/-- A heterogeneous, intrinsically checked vector of substitution images.
Unlike the external list, its source-context index records the exact type of
every position. -/
inductive TypedSubstitution (target : Ctx String) : Ctx String → Type where
  | nil : TypedSubstitution target []
  | cons {head : Ty String} {source : Ctx String} :
      Term Constant target head → TypedSubstitution target source →
        TypedSubstitution target (head :: source)

namespace TypedSubstitution

/-- Read a checked heterogeneous vector as the intrinsic HOL substitution it
represents. -/
def toSubst {target : Ctx String} :
  {source : Ctx String} → TypedSubstitution target source →
      Subst Constant source target
  | [], .nil => fun var => nomatch var
  | _head :: _source, .cons first rest =>
      fun var =>
        match var with
        | .vz => first
        | .vs prior => rest.toSubst prior

/-- Turn an intrinsic HOL substitution into its heterogeneous vector of
images, newest variable first. -/
def ofSubst {target : Ctx String} :
    {source : Ctx String} → Subst Constant source target →
      TypedSubstitution target source
  | [], _ => .nil
  | head :: source, substitution =>
      .cons (substitution (Var.vz : Var (head :: source) head))
        (ofSubst (source := source)
          (fun {type : Ty String} (var : Var source type) =>
            substitution (.vs var)))

@[simp] theorem toSubst_ofSubst_apply
    {source target : Ctx String}
    (substitution : Subst Constant source target)
    {type : Ty String} (var : Var source type) :
    (ofSubst substitution).toSubst var = substitution var := by
  induction source with
  | nil => exact nomatch var
  | cons head source inductionHypothesis =>
      cases var with
      | vz => simp [ofSubst, toSubst]
      | vs prior =>
          simpa [ofSubst, toSubst] using
            (inductionHypothesis
              (fun {type : Ty String} (tail : Var source type) =>
                substitution (.vs tail)) prior)

/-- Reconstructing the vector before acting on a term is observationally
identical to the original substitution. -/
theorem subst_toSubst_ofSubst
    {source target : Ctx String} {type : Ty String}
    (substitution : Subst Constant source target)
    (term : Term Constant source type) :
    subst (ofSubst substitution).toSubst term = subst substitution term := by
  exact subst_ext
    (fun var => toSubst_ofSubst_apply substitution var) term

end TypedSubstitution

/-- Encode a checked substitution vector newest variable first.  Duplicates
and order are retained. -/
def encodeImages {source target : Ctx String} :
    TypedSubstitution target source → List TermPacket
  | .nil => []
  | .cons first rest => encodeTerm first :: encodeImages rest

/-- Decode exactly one image per source variable, checking every image in the
same target context at the type prescribed by its source position. -/
def decodeImages? (target : Ctx String) :
    (source : Ctx String) → List TermPacket →
      Option (TypedSubstitution target source)
  | [], [] => some .nil
  | head :: source, first :: rest => do
      let decodedFirst ← decodeTerm? target first head
      let decodedRest ← decodeImages? target source rest
      pure (.cons decodedFirst decodedRest)
  | _, _ => none

@[simp] theorem decodeImages?_encodeImages
    {source target : Ctx String}
    (substitution : TypedSubstitution target source) :
    decodeImages? target source (encodeImages substitution) =
      some substitution := by
  induction substitution with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp [encodeImages, decodeImages?, inductionHypothesis]

/-! ## A portable substitution packet -/

/-- The source and target contexts are explicit runtime data.  `images` is an
ordered vector represented as a list; `decodeSubstitution?` checks its length,
scope, and heterogeneous component types. -/
structure SubstitutionPacket where
  source : Ctx String
  target : Ctx String
  images : List TermPacket
deriving Repr, DecidableEq

/-- Canonical packet for an intrinsic simultaneous substitution. -/
def encodeSubstitution {source target : Ctx String}
    (substitution : Subst Constant source target) : SubstitutionPacket where
  source := source
  target := target
  images := encodeImages (TypedSubstitution.ofSubst substitution)

/-- Fail-closed interpretation of a substitution packet. -/
def decodeSubstitution? (packet : SubstitutionPacket) :
    Option (TypedSubstitution packet.target packet.source) :=
  decodeImages? packet.target packet.source packet.images

@[simp] theorem decodeSubstitution?_encodeSubstitution
    {source target : Ctx String}
    (substitution : Subst Constant source target) :
    decodeSubstitution? (encodeSubstitution substitution) =
      some (TypedSubstitution.ofSubst substitution) := by
  simp [decodeSubstitution?, encodeSubstitution]

/-- Equal canonical packets imply pointwise equality of their intrinsic
substitutions.  This is the appropriate extensional injectivity statement for
the implicit, heterogeneous function type `Subst`. -/
theorem encodeSubstitution_reflects_pointwise_equality
    {source target : Ctx String}
    {first second : Subst Constant source target}
    (equal : encodeSubstitution first = encodeSubstitution second) :
    ∀ {type : Ty String} (var : Var source type),
      first var = second var := by
  have imagesEqual := congrArg SubstitutionPacket.images equal
  have decoded := congrArg (decodeImages? target source) imagesEqual
  simp [encodeSubstitution] at decoded
  intro type var
  calc
    first var = (TypedSubstitution.ofSubst first).toSubst var := by
      symm
      exact TypedSubstitution.toSubst_ofSubst_apply first var
    _ = (TypedSubstitution.ofSubst second).toSubst var := by rw [decoded]
    _ = second var :=
      TypedSubstitution.toSubst_ofSubst_apply second var

/-! ## Executable action and reflection -/

/-- Apply a decoded substitution to a decoded term and return the exact
canonical target-context packet. -/
def substitutePacket? (substitution : SubstitutionPacket)
    (type : TypePacket) (term : TermPacket) : Option TermPacket := do
  let decodedSubstitution ← decodeSubstitution? substitution
  let decodedTerm ← decodeTerm? substitution.source term type.decode
  pure (encodeTerm (subst decodedSubstitution.toSubst decodedTerm))

@[simp] theorem substitutePacket?_encode
    {source target : Ctx String} {type : Ty String}
    (substitution : Subst Constant source target)
    (term : Term Constant source type) :
    substitutePacket? (encodeSubstitution substitution)
        (TypePacket.encode type) (encodeTerm term) =
      some (encodeTerm (subst substitution term)) := by
  unfold substitutePacket?
  rw [show decodeSubstitution? (encodeSubstitution substitution) =
      some (TypedSubstitution.ofSubst substitution) from
    decodeSubstitution?_encodeSubstitution substitution]
  change (do
      let decodedTerm ← decodeTerm? source (encodeTerm term) type
      pure (encodeTerm
        (subst (TypedSubstitution.ofSubst substitution).toSubst
          decodedTerm))) = _
  rw [decodeTerm?_encodeTerm]
  change some (encodeTerm
      (subst (TypedSubstitution.ofSubst substitution).toSubst term)) = _
  rw [TypedSubstitution.subst_toSubst_ofSubst]

/-- Every accepted request is exactly an intrinsic typed simultaneous
substitution. -/
theorem substitutePacket?_reflects
    {substitution : SubstitutionPacket} {type : TypePacket}
    {term result : TermPacket}
    (accepted : substitutePacket? substitution type term = some result) :
    ∃ (decodedSubstitution :
          TypedSubstitution substitution.target substitution.source)
      (decodedTerm :
          Term Constant substitution.source type.decode),
      decodeSubstitution? substitution = some decodedSubstitution ∧
      decodeTerm? substitution.source term type.decode = some decodedTerm ∧
      result = encodeTerm (subst decodedSubstitution.toSubst decodedTerm) := by
  cases substitutionDecoded : decodeSubstitution? substitution with
  | none =>
      simp [substitutePacket?, substitutionDecoded] at accepted
  | some decodedSubstitution =>
      cases termDecoded :
          decodeTerm? substitution.source term type.decode with
      | none =>
          simp [substitutePacket?, substitutionDecoded, termDecoded] at accepted
      | some decodedTerm =>
          simp [substitutePacket?, substitutionDecoded, termDecoded] at accepted
          exact ⟨decodedSubstitution, decodedTerm, rfl, rfl, accepted.symm⟩

/-- Accepted output re-enters the target-context decoder as the exact
intrinsic substituted term. -/
theorem substitutePacket?_output_decodes
    {substitution : SubstitutionPacket} {type : TypePacket}
    {term result : TermPacket}
    (accepted : substitutePacket? substitution type term = some result) :
    ∃ (decodedSubstitution :
          TypedSubstitution substitution.target substitution.source)
      (decodedTerm :
          Term Constant substitution.source type.decode),
      decodeSubstitution? substitution = some decodedSubstitution ∧
      decodeTerm? substitution.source term type.decode = some decodedTerm ∧
      decodeTerm? substitution.target result type.decode =
        some (subst decodedSubstitution.toSubst decodedTerm) := by
  obtain ⟨decodedSubstitution, decodedTerm, substitutionDecoded, termDecoded,
      resultEncoded⟩ := substitutePacket?_reflects accepted
  subst result
  exact ⟨decodedSubstitution, decodedTerm, substitutionDecoded, termDecoded,
    decodeTerm?_encodeTerm _⟩

/-! ## Identity and composition laws -/

/-- The canonical identity packet acts as identity. -/
theorem substitutePacket?_identity
    {context : Ctx String} {type : Ty String}
    (term : Term Constant context type) :
    substitutePacket?
        (encodeSubstitution
          (Subst.id (Base := String) (Const := Constant) (Γ := context)))
        (TypePacket.encode type) (encodeTerm term) =
      some (encodeTerm term) := by
  simp [substitutePacket?_encode,
    Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary.th0_substitution_identity]

/-- Applying a canonical composite agrees with applying its two components in
sequence.  This is the substitution-category law at the portable boundary. -/
theorem substitutePacket?_composition
    {source middle target : Ctx String} {type : Ty String}
    (later : Subst Constant middle target)
    (earlier : Subst Constant source middle)
    (term : Term Constant source type) :
    substitutePacket?
        (encodeSubstitution (Subst.comp later earlier))
        (TypePacket.encode type) (encodeTerm term) =
      (do
        let intermediate ← substitutePacket?
          (encodeSubstitution earlier)
          (TypePacket.encode type) (encodeTerm term)
        substitutePacket? (encodeSubstitution later)
          (TypePacket.encode type) intermediate) := by
  simp [substitutePacket?_encode,
    Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary.th0_substitution_composition]

/-! ## Canonical wire representation -/

def encodeContextWire (context : Ctx String) : WireTerm :=
  .list (context.map encodeTyWire)

def decodeTypeList : List WireTerm → Option (Ctx String)
  | [] => some []
  | type :: types => do
      let decodedType ← decodeTyWire type
      let decodedTypes ← decodeTypeList types
      pure (decodedType :: decodedTypes)

def decodeContextWire : WireTerm → Option (Ctx String)
  | .list types => decodeTypeList types
  | _ => none

@[simp] theorem decodeTypeList_map_encode
    (context : Ctx String) :
    decodeTypeList (context.map encodeTyWire) = some context := by
  induction context with
  | nil => rfl
  | cons type context inductionHypothesis =>
      simp [decodeTypeList, inductionHypothesis]

@[simp] theorem decodeContextWire_encodeContextWire
    (context : Ctx String) :
    decodeContextWire (encodeContextWire context) = some context := by
  simp [decodeContextWire, encodeContextWire]

def encodeTermListWire (terms : List TermPacket) : WireTerm :=
  .list (terms.map encodeTermWire)

def decodeTermList : List WireTerm → Option (List TermPacket)
  | [] => some []
  | term :: terms => do
      let decodedTerm ← decodeTermWire term
      let decodedTerms ← decodeTermList terms
      pure (decodedTerm :: decodedTerms)

def decodeTermListWire : WireTerm → Option (List TermPacket)
  | .list terms => decodeTermList terms
  | _ => none

@[simp] theorem decodeTermList_map_encode
    (terms : List TermPacket) :
    decodeTermList (terms.map encodeTermWire) = some terms := by
  induction terms with
  | nil => rfl
  | cons term terms inductionHypothesis =>
      simp [decodeTermList, inductionHypothesis]

@[simp] theorem decodeTermListWire_encodeTermListWire
    (terms : List TermPacket) :
    decodeTermListWire (encodeTermListWire terms) = some terms := by
  simp [decodeTermListWire, encodeTermListWire]

def substitutionWireVersion : Nat := 1

def encodeSubstitutionWire (packet : SubstitutionPacket) : WireTerm :=
  .list [.symbol "TH0Substitution", .natural substitutionWireVersion,
    encodeContextWire packet.source, encodeContextWire packet.target,
    encodeTermListWire packet.images]

def decodeSubstitutionWire : WireTerm → Option SubstitutionPacket
  | .list [.symbol "TH0Substitution", .natural version,
      source, target, images] => do
      if version != substitutionWireVersion then none
      let decodedSource ← decodeContextWire source
      let decodedTarget ← decodeContextWire target
      let decodedImages ← decodeTermListWire images
      pure ⟨decodedSource, decodedTarget, decodedImages⟩
  | _ => none

@[simp] theorem decodeSubstitutionWire_encodeSubstitutionWire
    (packet : SubstitutionPacket) :
    decodeSubstitutionWire (encodeSubstitutionWire packet) = some packet := by
  cases packet
  simp [decodeSubstitutionWire, encodeSubstitutionWire,
    substitutionWireVersion]

theorem encodeSubstitutionWire_injective :
    Function.Injective encodeSubstitutionWire := by
  intro first second equal
  have decoded := congrArg decodeSubstitutionWire equal
  simpa using decoded

theorem decodeSubstitutionWire_rejects_future_version
    (packet : SubstitutionPacket) :
    decodeSubstitutionWire
        (.list [.symbol "TH0Substitution",
          .natural (substitutionWireVersion + 1),
          encodeContextWire packet.source, encodeContextWire packet.target,
          encodeTermListWire packet.images]) = none := by
  simp [decodeSubstitutionWire, substitutionWireVersion]

/-- Parse and execute one complete symbolic substitution request. -/
def substituteWire? (substitutionWire typeWire termWire : WireTerm) :
    Option WireTerm := do
  let substitution ← decodeSubstitutionWire substitutionWire
  let type ← decodeTypeWire typeWire
  let term ← decodeTermWire termWire
  let result ← substitutePacket? substitution type term
  pure (encodeTermWire result)

@[simp] theorem substituteWire?_encode
    {source target : Ctx String} {type : Ty String}
    (substitution : Subst Constant source target)
    (term : Term Constant source type) :
    substituteWire?
        (encodeSubstitutionWire (encodeSubstitution substitution))
        (encodeTypeWire (TypePacket.encode type))
        (encodeTermWire (encodeTerm term)) =
      some (encodeTermWire (encodeTerm (subst substitution term))) := by
  simp [substituteWire?]

/-! ## Independent replay and dialect bindings -/

/-- A candidate substitution step.  Search procedures may propose claims, but
the authority below accepts them only by replaying the pure packet service. -/
structure SubstitutionClaim where
  substitution : SubstitutionPacket
  type : TypePacket
  term : TermPacket
  result : TermPacket
deriving Repr

structure SubstitutionEvidence (claim : SubstitutionClaim) where
  replay : substitutePacket? claim.substitution claim.type claim.term =
    some claim.result

structure SubstitutionObstruction (claim : SubstitutionClaim) where
  replay : substitutePacket? claim.substitution claim.type claim.term ≠
    some claim.result

def substitutionAuthority : Authority SubstitutionClaim where
  Holds claim :=
    substitutePacket? claim.substitution claim.type claim.term =
      some claim.result
  Evidence := SubstitutionEvidence
  Obstruction := SubstitutionObstruction
  evidenceSound := by
    intro claim evidence
    exact evidence.replay
  obstructionSound := by
    intro claim obstruction evidence
    exact obstruction.replay evidence

def checkSubstitution (claim : SubstitutionClaim) :
    Outcome (SubstitutionEvidence claim) (SubstitutionObstruction claim)
      Unit Unit :=
  if replay : substitutePacket? claim.substitution claim.type claim.term =
      some claim.result then
    .established ⟨replay⟩
  else
    .refuted ⟨replay⟩

theorem substitutionEvidence_reflects
    {claim : SubstitutionClaim}
    (evidence : SubstitutionEvidence claim) :
    ∃ (decodedSubstitution :
          TypedSubstitution claim.substitution.target
            claim.substitution.source)
      (decodedTerm :
          Term Constant claim.substitution.source claim.type.decode),
      decodeSubstitution? claim.substitution = some decodedSubstitution ∧
      decodeTerm? claim.substitution.source claim.term claim.type.decode =
        some decodedTerm ∧
      claim.result = encodeTerm
        (subst decodedSubstitution.toSubst decodedTerm) :=
  substitutePacket?_reflects evidence.replay

/-- Implementations may choose different internal representations.  A binding
is conforming precisely when its public wire operation agrees with the
reference service for every request. -/
structure WireSubstitutionAdapter where
  execute : WireTerm → WireTerm → WireTerm → Option WireTerm
  agrees : ∀ substitution type term,
    execute substitution type term = substituteWire? substitution type term

/-- Any two conforming bindings—whether used by HE, PeTTa, Prime, or generated
native code—have identical observable TH0 substitution behavior.  The theorem
does not assert that a runtime binding already exists. -/
theorem conforming_adapters_agree
    (first second : WireSubstitutionAdapter)
    (substitution type term : WireTerm) :
    first.execute substitution type term =
      second.execute substitution type term := by
  rw [first.agrees, second.agrees]

/-! ## Positive and negative controls -/

namespace Canary

def individualType : Ty String := .base "individual"

def firstTarget : Term Constant [individualType, individualType]
    individualType := .var .vz

def secondTarget : Term Constant [individualType, individualType]
    individualType := .var (.vs .vz)

/-- Two equal-typed source variables deliberately receive different ordered
images, demonstrating that the packet is not a set or name-indexed map. -/
def swapSubstitution :
    Subst Constant [individualType, individualType]
      [individualType, individualType]
  | _, .vz => secondTarget
  | _, .vs .vz => firstTarget
  | _, .vs (.vs var) => nomatch var

theorem ordered_swap_is_preserved :
    (encodeSubstitution swapSubstitution).images =
      [encodeTerm secondTarget, encodeTerm firstTarget] :=
  rfl

def newestVariable :
    Term Constant [individualType, individualType] individualType :=
  .var .vz

theorem swap_substitutes_newest :
    subst swapSubstitution newestVariable = secondTarget := by
  rfl

theorem swap_executes :
    substitutePacket? (encodeSubstitution swapSubstitution)
        (TypePacket.encode individualType) (encodeTerm newestVariable) =
      some (encodeTerm secondTarget) := by
  calc
    substitutePacket? (encodeSubstitution swapSubstitution)
        (TypePacket.encode individualType) (encodeTerm newestVariable) =
      some (encodeTerm (subst swapSubstitution newestVariable)) :=
        substitutePacket?_encode swapSubstitution newestVariable
    _ = some (encodeTerm secondTarget) := by
      rw [swap_substitutes_newest]

/-- One missing image is rejected even though its surviving component is
well-typed. -/
def shortPacket : SubstitutionPacket where
  source := [individualType, individualType]
  target := [individualType, individualType]
  images := [encodeTerm secondTarget]

theorem short_packet_rejected :
    decodeSubstitution? shortPacket = none := by
  simp [decodeSubstitution?, shortPacket, decodeImages?]

/-- A component scoped in a two-variable context cannot be laundered as a
closed target image. -/
def outOfScopePacket : SubstitutionPacket where
  source := [individualType]
  target := []
  images := [encodeTerm firstTarget]

theorem out_of_scope_packet_rejected :
    decodeSubstitution? outOfScopePacket = none := by
  simp [decodeSubstitution?, outOfScopePacket, decodeImages?,
    firstTarget, decodeTerm?, encodeTerm, decodeVar?]

/-- A proposition-valued image cannot fill an individual-valued source slot. -/
def wrongTypePacket : SubstitutionPacket where
  source := [individualType]
  target := []
  images := [TermPacket.top]

theorem wrong_type_packet_rejected :
    decodeSubstitution? wrongTypePacket = none := by
  simp [decodeSubstitution?, wrongTypePacket, decodeImages?, decodeTerm?,
    individualType]

theorem substitution_service_boundary :
    substitutePacket? (encodeSubstitution swapSubstitution)
        (TypePacket.encode individualType) (encodeTerm newestVariable) =
        some (encodeTerm secondTarget) ∧
      decodeSubstitution? shortPacket = none ∧
      decodeSubstitution? outOfScopePacket = none ∧
      decodeSubstitution? wrongTypePacket = none ∧
      HORequirement.higherOrderUnification ∉ substitutionKernelRequirements := by
  exact ⟨swap_executes, short_packet_rejected,
    out_of_scope_packet_rejected, wrong_type_packet_rejected,
    substitution_does_not_discharge_unification⟩

end Canary

#print axioms decodeImages?_encodeImages
#print axioms decodeSubstitution?_encodeSubstitution
#print axioms encodeSubstitution_reflects_pointwise_equality
#print axioms substitutePacket?_encode
#print axioms substitutePacket?_reflects
#print axioms substitutePacket?_output_decodes
#print axioms substitutePacket?_identity
#print axioms substitutePacket?_composition
#print axioms decodeSubstitutionWire_encodeSubstitutionWire
#print axioms encodeSubstitutionWire_injective
#print axioms decodeSubstitutionWire_rejects_future_version
#print axioms substituteWire?_encode
#print axioms substitutionEvidence_reflects
#print axioms conforming_adapters_agree
#print axioms Canary.ordered_swap_is_preserved
#print axioms Canary.swap_executes
#print axioms Canary.short_packet_rejected
#print axioms Canary.out_of_scope_packet_rejected
#print axioms Canary.wrong_type_packet_rejected
#print axioms Canary.substitution_service_boundary

end Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService
