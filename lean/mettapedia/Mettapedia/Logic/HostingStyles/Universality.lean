import Mettapedia.Logic.HostingStyles.Catamorphisms

/-!
# Universal hosts: top degrees of the hosting preorder

A theory `host` **hosts every** theory of a class when each member has a
hosting map into it (`HostsEvery`).  This is weak terminality: for the
category of theories presented through their contexts
(`Mettapedia.GSLT.ContextTheory`, with its maps `ContextMap`), every object of
the class has *some* hosting map into the host.  Nothing says the map is
unique, and it is not (`propTheory_two_hostings`).  A hosting map preserves
and reflects what every probe sees (`ContextMap.Hosting.bisimilar_push_iff`),
so no probe needs to be named in the definition.  For proof systems, which
have no reduction, the question a probe would ask is asked instead by the
congruence at which the source is taken: derivations kept apart, or only
provability.

A hosting map may in addition be exhausting; then the host adds nothing
between the images (`HostsExhaustively`).

## The three styles as universality statements

* **Shallow semantic.**  The host's own propositions form a theory
  (`propTheory`): an interface is a proposition, a term is its proof, a
  context is an entailment.  It hosts the provability collapse of every
  finitary proof system (`propTheory_hostsEvery_provability`).  It hosts no
  proof system, at the level where derivations are kept apart, in which some
  judgment has two derivations (`not_hosting_into_total`): any theory whose
  terms are all identified forgets them.  So a host logic under shallow
  embedding is universal for provability and for nothing finer.
* **Judgments as types.**  For any family of finitary proof systems indexed
  by a type, the framework over the union of their signatures
  (`universalFramework`) hosts every member with its derivations kept apart
  (`universalFramework_hostsEvery`).  The map is the inclusion into the union
  followed by the rules-as-constants encoding.
* **Native.**  The theory of a proof system is defined for every rule
  signature, and it hosts and exhausts itself by the identity
  (`native_hostsExhaustively`).  No single host object is involved: the
  construction is generic over the category.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

universe v

/-! ## The definition -/

/-- **A host hosts every theory of a class**: each member has a hosting map
into it.  Existence, not uniqueness. -/
def HostsEvery (host : ContextTheory.{0}) (sources : ContextTheory.{0} → Prop) : Prop :=
  ∀ source, sources source → ∃ map : ContextMap source host, map.Hosting

/-- A source is hosted with nothing added: some hosting map into the host is
also exhausting. -/
def HostsExhaustively (host source : ContextTheory.{0}) : Prop :=
  ∃ map : ContextMap source host, map.Hosting ∧ map.Exhausting

/-- A host of a class hosts every smaller class. -/
theorem HostsEvery.mono {host : ContextTheory.{0}} {larger smaller : ContextTheory.{0} → Prop}
    (hosts : HostsEvery host larger) (subclass : ∀ source, smaller source → larger source) :
    HostsEvery host smaller :=
  fun source member => hosts source (subclass source member)

/-- A host that is itself hosted passes its class on. -/
theorem HostsEvery.trans {host larger : ContextTheory.{0}} {sources : ContextTheory.{0} → Prop}
    (hosts : HostsEvery host sources) {map : ContextMap host larger} (hosting : map.Hosting) :
    HostsEvery larger sources := by
  intro source member
  obtain ⟨first, firstHosting⟩ := hosts source member
  exact ⟨map.comp first, hosting.comp firstHosting⟩

/-- Hosting and exhausting compose. -/
theorem HostsExhaustively.trans {first second third : ContextTheory.{0}}
    (lower : HostsExhaustively second first) (upper : HostsExhaustively third second) :
    HostsExhaustively third first := by
  obtain ⟨lowerMap, lowerHosting, lowerExhausting⟩ := lower
  obtain ⟨upperMap, upperHosting, upperExhausting⟩ := upper
  exact ⟨upperMap.comp lowerMap, upperHosting.comp lowerHosting,
    upperExhausting.comp lowerExhausting⟩

/-! ## Native: the identity -/

/-- **Every proof system hosts and exhausts itself**, at every congruence. -/
theorem native_hostsExhaustively {J : Type} (P : RuleSignature J)
    (congruence : P.ProofCongruence) :
    HostsExhaustively (P.proofTheory congruence) (P.proofTheory congruence) :=
  ⟨ContextMap.id _, P.native_hosting congruence, P.native_exhausting congruence⟩

/-! ## Shallow: the host's propositions -/

/-- **The theory of the host's propositions.**  An interface is a
proposition, a term is its proof, a context is an entailment from finitely
many assumptions. -/
def propTheory : ContextTheory.{0} :=
  shallowTheory (Point := PUnit.{1}) (J := Prop) fun _ proposition => proposition

section Validity

variable {J : Type} {Point : Type v} (holds : Point → J → Prop)

/-- Reading a judgment as the host proposition that it is valid: a map from
the theory of a semantics to the theory of the host's propositions. -/
def validityMap : ContextMap (shallowTheory holds) propTheory where
  interface := fun j => Valid holds j
  term := fun valid => ⟨fun _ => valid.down⟩
  context := fun context => ⟨by
    obtain ⟨support, follows⟩ := context.down
    exact ⟨support, fun _ assumed point => follows point fun index member =>
      assumed index member point⟩⟩
  term_resp := fun _ => trivial
  equivariant := fun _ _ => trivial

/-- Reading validity as a host proposition is hosting: no truth is
identified with another that was apart. -/
theorem validityMap_hosting : (validityMap holds).Hosting := by
  rw [ContextMap.hosting_iff]
  exact ⟨fun _ => trivial, fun _ _ _ step => step.elim, fun _ _ _ step => step.elim⟩

end Validity

/-- The semantics every proof system has: a judgment holds when it has a
derivation. -/
def provableHolds {J : Type} (P : RuleSignature J) (_ : PUnit.{1}) (j : J) : Prop :=
  Nonempty (P.Proof j)

theorem provable_locallySound {J : Type} (P : RuleSignature J) :
    LocallySound (provableHolds P) P :=
  fun shape _ each => P.derivable_ruleClosed _ shape each

/-- **The theory of the host's propositions hosts the provability collapse of
a finitary proof system.** -/
theorem propTheory_hosts_provability {J : Type} {P : RuleSignature J} (finitary : P.Finitary) :
    ∃ map : ContextMap (P.proofTheory (RuleSignature.ProofCongruence.total P)) propTheory,
      map.Hosting :=
  ⟨(validityMap (provableHolds P)).comp
      (shallowMap (provable_locallySound P) finitary (RuleSignature.ProofCongruence.total P)),
    (validityMap_hosting _).comp (shallowMap_hosting_total (provable_locallySound P) finitary)⟩

/-- The provability collapses of the finitary proof systems. -/
def ProvabilityCollapse (source : ContextTheory.{0}) : Prop :=
  ∃ (J : Type) (P : RuleSignature J) (_ : P.Finitary),
    source = P.proofTheory (RuleSignature.ProofCongruence.total P)

/-- **The host's propositions are a universal host for provability.** -/
theorem propTheory_hostsEvery_provability : HostsEvery propTheory ProvabilityCollapse := by
  rintro source ⟨J, P, finitary, rfl⟩
  exact propTheory_hosts_provability finitary

/-- **A theory whose terms are all identified hosts no proof system in which
two derivations are kept apart.** -/
theorem not_hosting_into_total {J : Type} {P : RuleSignature J} {target : ContextTheory.{0}}
    (identified : ∀ (interface : target.Interface) (first second : target.Term interface),
      (target.equations interface).r first second)
    (map : ContextMap (P.proofTheory (RuleSignature.ProofCongruence.identity P)) target) {j : J}
    {first second : P.Proof j} (distinct : first ≠ second) : ¬ map.Hosting :=
  ContextMap.not_hosting_of_identifies map distinct (identified _ _ _)

/-- In particular the host's propositions do not host the worked logic with
its derivations kept apart. -/
theorem propTheory_not_hosting_int
    (map : ContextMap (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))
      propTheory) : ¬ map.Hosting :=
  not_hosting_into_total (fun _ _ _ => trivial) map (identityProof_ne_detourProof (.atom 0))

/-- **Hosting maps into a universal host are not unique.**  The worked logic,
at its provability collapse, has two hosting maps into the host's
propositions that send Peirce's law to different propositions: one reads it
by truth tables, the other by provability. -/
theorem propTheory_two_hostings :
    ∃ first second : ContextMap
        (intSignature.proofTheory (RuleSignature.ProofCongruence.total intSignature)) propTheory,
      first.Hosting ∧ second.Hosting ∧ first.interface peirce ≠ second.interface peirce := by
  refine ⟨(validityMap truthTableHolds).comp (truthTableMap _),
    (validityMap (provableHolds intSignature)).comp
      (shallowMap (provable_locallySound intSignature) intFinitary _),
    (validityMap_hosting _).comp truthTableMap_hosting_total,
    (validityMap_hosting _).comp (shallowMap_hosting_total _ intFinitary), ?_⟩
  intro same
  have valid : Valid truthTableHolds peirce := truthTable_peirce
  have provable : Valid (provableHolds intSignature) peirce := by
    have transported : (Valid truthTableHolds peirce : Prop) =
        Valid (provableHolds intSignature) peirce := same
    rw [← transported]
    exact valid
  exact (provable PUnit.unit).elim peirce_underivable.false

/-! ## Judgments as types: one framework for a family -/

section Family

variable {Index : Type} {J : Index → Type} (P : (index : Index) → RuleSignature (J index))

/-- **The union of a family of proof systems**: a judgment is a judgment of
one member, and its rules are that member's. -/
def sumSignature : RuleSignature (Σ index, J index) where
  Shape := fun _ judgment => (P judgment.1).Shape PUnit.unit judgment.2
  Position := fun {_ judgment} shape => (P judgment.1).Position shape
  next := fun {_ judgment} shape position => ⟨judgment.1, (P judgment.1).next shape position⟩

/-- The premises of the rules of the union are numbered as in the members. -/
def sumFinitary (finitary : (index : Index) → (P index).Finitary) : (sumSignature P).Finitary where
  arity := fun {judgment} shape => (finitary judgment.1).arity shape
  position := fun {judgment} shape => (finitary judgment.1).position shape

/-- A derivation of a member, as a derivation of the union. -/
noncomputable def inject (index : Index) {j : J index} (proof : (P index).Proof j) :
    (sumSignature P).Proof ⟨index, j⟩ :=
  Fix.fold (P index) (carrier := fun _ j => (sumSignature P).Proof ⟨index, j⟩)
    (fun _ _ layer => (sumSignature P).node (j := ⟨index, _⟩) layer.1 layer.2) PUnit.unit j proof

/-- A derived rule of a member, as a derived rule of the union. -/
noncomputable def injectContext (index : Index) {arity : Type} {assumptions : arity → J index}
    {j : J index} (context : (P index).Open assumptions j) :
    (sumSignature P).Open (fun slot => (⟨index, assumptions slot⟩ : Σ index, J index))
      ⟨index, j⟩ :=
  Free.fold (P index)
    (fun _ _ hole => RuleSignature.HoleAt.elim
      (motive := fun j => (sumSignature P).Open
        (fun slot => (⟨index, assumptions slot⟩ : Σ index, J index)) ⟨index, j⟩)
      (fun slot => (sumSignature P).assume slot) hole)
    { act := fun _ _ layer => Free.node (sumSignature P) (index := ⟨index, _⟩) layer.1 layer.2 }
    PUnit.unit j context

/-- A derivation of the union is a derivation of the member its judgment
belongs to. -/
noncomputable def project {judgment : Σ index, J index} (proof : (sumSignature P).Proof judgment) :
    (P judgment.1).Proof judgment.2 :=
  Fix.fold (sumSignature P) (carrier := fun _ judgment => (P judgment.1).Proof judgment.2)
    (fun _ judgment layer => (P judgment.1).node layer.1 layer.2) PUnit.unit judgment proof

theorem project_inject (index : Index) {j : J index} (proof : (P index).Proof j) :
    project P (inject P index proof) = proof := by
  induction proof using RuleSignature.Proof.induction with
  | node shape children ih =>
      change (P index).node shape (fun position => project P (inject P index (children position))) = _
      exact congrArg ((P index).node shape) (funext ih)

theorem inject_fill (index : Index) {arity : Type} {assumptions : arity → J index} {j : J index}
    (context : (P index).Open assumptions j)
    (filling : (slot : arity) → (P index).Proof (assumptions slot)) :
    inject P index ((P index).fill context filling) =
      (sumSignature P).fill (injectContext P index context) fun slot =>
        inject P index (filling slot) := by
  induction context using RuleSignature.Open.induction with
  | assume slot => rfl
  | node shape children ih =>
      change (sumSignature P).node (j := ⟨index, _⟩) shape
          (fun position => inject P index ((P index).fill (children position) filling)) =
        (sumSignature P).node (j := ⟨index, _⟩) shape
          (fun position => (sumSignature P).fill (injectContext P index (children position)) _)
      exact congrArg _ (funext ih)

/-- **The inclusion of a member into the union**, as a map of theories. -/
noncomputable def injectMap (index : Index) :
    ContextMap ((P index).proofTheory (RuleSignature.ProofCongruence.identity _))
      ((sumSignature P).proofTheory (RuleSignature.ProofCongruence.identity _)) where
  interface := fun j => ⟨index, j⟩
  term := fun proof => inject P index proof
  context := fun context => injectContext P index context
  term_resp := fun same => congrArg (inject P index) same
  equivariant := fun context filling => inject_fill P index context filling

/-- The inclusion is hosting: it identifies no two derivations. -/
theorem injectMap_hosting (index : Index) : (injectMap P index).Hosting := by
  rw [(P index).hosting_iff_static _ _ (fun _ _ step => step)]
  intro j first second same
  have equal : inject P index first = inject P index second := same
  have projected := congrArg (project P) equal
  exact (project_inject P index first).symm.trans
    (projected.trans (project_inject P index second))

/-- **One framework for the family**: the framework over the signature of the
union. -/
def universalFramework (finitary : (index : Index) → (P index).Finitary) : ContextTheory.{0} :=
  frameworkTheory (sumFinitary P finitary).signature

/-- **The framework hosts every member of the family, with its derivations
kept apart.** -/
theorem universalFramework_hosts (finitary : (index : Index) → (P index).Finitary)
    (index : Index) :
    ∃ map : ContextMap ((P index).proofTheory (RuleSignature.ProofCongruence.identity _))
        (universalFramework P finitary), map.Hosting :=
  ⟨(sumFinitary P finitary).encodingMap.comp (injectMap P index),
    (sumFinitary P finitary).encodingMap_hosting.comp (injectMap_hosting P index)⟩

/-- The members of the family, with derivations kept apart. -/
def FamilyMember (source : ContextTheory.{0}) : Prop :=
  ∃ index, source = (P index).proofTheory (RuleSignature.ProofCongruence.identity _)

/-- **The framework is a universal host for the family.** -/
theorem universalFramework_hostsEvery (finitary : (index : Index) → (P index).Finitary) :
    HostsEvery (universalFramework P finitary) (FamilyMember P) := by
  rintro source ⟨index, rfl⟩
  exact universalFramework_hosts P finitary index

/-- The union is hosted by its framework with nothing added. -/
theorem universalFramework_exhausts_union (finitary : (index : Index) → (P index).Finitary) :
    HostsExhaustively (universalFramework P finitary)
      ((sumSignature P).proofTheory (RuleSignature.ProofCongruence.identity _)) :=
  ⟨(sumFinitary P finitary).encodingMap, (sumFinitary P finitary).encodingMap_hosting,
    (sumFinitary P finitary).encodingMap_exhausting⟩

end Family

#print axioms propTheory_hostsEvery_provability
#print axioms not_hosting_into_total
#print axioms propTheory_two_hostings
#print axioms injectMap_hosting
#print axioms universalFramework_hostsEvery
#print axioms universalFramework_exhausts_union
#print axioms native_hostsExhaustively

end Mettapedia.Logic.HostingStyles
