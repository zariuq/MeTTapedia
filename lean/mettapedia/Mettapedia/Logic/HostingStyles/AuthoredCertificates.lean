import Mettapedia.Logic.HostingStyles.UniversalityAnchors
import Mettapedia.Logic.HostingStyles.ProofNodes
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayBijection

/-!
# Certificates of an authored calculus, read as derivations

`UniversalityAnchors` states that the checker of an authored calculus accepts
exactly the derivable goals: a hosting and exhausting map at the level of
provability.  This module raises the statement to derivations kept apart.

## Two rule signatures

* `derivationSignature K`: a node is a rule instance of the calculus or a
  fact of its authored family.  Its derivations are the proof-relevant form of
  the existing `AuthoredCalculus.Derivable` (`nonempty_tree_iff_derivable`).
* `certificateSignature K`: a node is a rule instance, a computed leaf that
  returns the goal, or an accepted raw replay tree.  Its derivations are the
  accepted certificates of the specified checker, exactly
  (`certificateEquiv`): erasing the evidence is a bijection onto the
  certificates that `check` accepts.

## Reading and writing

`read` sends a certificate to the derivation it stands for: a rule node to a
rule node, a computed leaf to the fact it returns, and a raw replay tree to
the derivation that it is (`BootstrapCell.derivationOf`).  `write` sends a
derivation to a certificate.  Reading after writing is the identity
(`read_write`).

* **Raw replay certificates are in bijection with derivations**
  (`BootstrapCell.checkedEquiv`).
* **Compact certificates are not**: a computed leaf may be run with more
  fuel, and a replay tree may be opened into rule nodes.  A certificate with a
  replay tree at its root differs from the certificate written from its
  reading and has the same reading (`replay_ne_write_read`).
* **Up to their reading they are**: certificates compared by the derivation
  they stand for are in bijection with derivations (`readEquiv`).

## The statement in the category of theories

`writeMap K` is a map from the proof theory of the calculus, with its
derivations kept apart, to the theory of its certificates compared by their
reading.  It is hosting and exhausting
(`authoredCalculus_hosts_derivations`).  With certificates compared by
identity it is still hosting (`writeStrictMap_hosting`): two derivations
never share a certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)
open Mettapedia.GSLT.LanguageDef.InferenceChecker
  (RuleInstance RawProof RuleApplication instantiateRule? checkRaw DerivationList
    instantiateRule?_eq_some_iff_application)
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check checkChildren)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.BootstrapCell (derivationOf derivationOf_erase)

/-! ## The two signatures -/

/-- A node of a derivation of an authored calculus: a rule instance, or a
fact of its family. -/
inductive DerivationShape (K : AuthoredCalculus) (goal : Pattern) : Type where
  | byRule (ruleInstance : RuleInstance) (premises : List Pattern)
      (application : RuleApplication K.definition ruleInstance premises goal)
  | fact (holds : K.family.Fact goal)

/-- The premises of a node. -/
def DerivationShape.premises {K : AuthoredCalculus} {goal : Pattern} :
    DerivationShape K goal → List Pattern
  | .byRule _ premises _ => premises
  | .fact _ => []

/-- **The rule signature of an authored calculus.** -/
def derivationSignature (K : AuthoredCalculus) : RuleSignature Pattern where
  Shape := fun _ goal => DerivationShape K goal
  Position := fun shape => Fin shape.premises.length
  next := fun shape position => shape.premises.get position

/-- A node of a certificate: a rule instance, a computed leaf that returns the
goal, or a raw replay tree accepted for the goal. -/
inductive CertificateShape (K : AuthoredCalculus) (goal : Pattern) : Type where
  | node (ruleInstance : RuleInstance) (premises : List Pattern)
      (application : RuleApplication K.definition ruleInstance premises goal)
  | computed (leaf : K.family.Leaf) (returned : K.family.evaluate leaf = some goal)
  | replay (raw : RawProof) (accepted : checkRaw K.definition goal raw = true)

/-- The premises of a certificate node. -/
def CertificateShape.premises {K : AuthoredCalculus} {goal : Pattern} :
    CertificateShape K goal → List Pattern
  | .node _ premises _ => premises
  | .computed _ _ => []
  | .replay _ _ => []

/-- **The rule signature of the certificates of an authored calculus.** -/
def certificateSignature (K : AuthoredCalculus) : RuleSignature Pattern where
  Shape := fun _ goal => CertificateShape K goal
  Position := fun shape => Fin shape.premises.length
  next := fun shape position => shape.premises.get position

variable (K : AuthoredCalculus)

/-- The premises of both signatures are numbered. -/
def derivationFinitary : (derivationSignature K).Finitary where
  arity := fun shape => shape.premises.length
  position := fun _ => Equiv.refl _

def certificateFinitary : (certificateSignature K).Finitary where
  arity := fun shape => shape.premises.length
  position := fun _ => Equiv.refl _

/-! ## Derivations are the proof-relevant form of derivability -/

/-- **A goal has a derivation exactly when it is derivable** from the rules
and the facts, in the existing sense. -/
theorem nonempty_tree_iff_derivable (goal : Pattern) :
    Nonempty ((derivationSignature K).Proof goal) ↔ K.Derivable goal := by
  constructor
  · rintro ⟨tree⟩
    induction tree using RuleSignature.Proof.induction with
    | node shape children ih =>
        cases shape with
        | byRule ruleInstance premises application =>
            refine FactDerivation.byRule ruleInstance application fun premise member => ?_
            obtain ⟨position, rfl⟩ := List.mem_iff_get.mp member
            exact ih position
        | fact holds => exact FactDerivation.fact holds
  · intro derived
    induction derived with
    | fact holds =>
        exact ⟨(derivationSignature K).node (.fact holds) fun position => position.elim0⟩
    | @byRule ruleInstance premises conclusion application _ ih =>
        exact ⟨(derivationSignature K).node (.byRule ruleInstance premises application)
          fun position => Classical.choice (ih _ (List.get_mem premises position))⟩

/-! ## Writing a derivation as a certificate -/

/-- One layer of writing, into any family that has the nodes of
certificates. -/
noncomputable def writeLayer {carrier : PUnit.{1} → Pattern → Type}
    (build : ∀ {goal : Pattern} (shape : CertificateShape K goal),
      ((position : Fin shape.premises.length) →
        carrier PUnit.unit (shape.premises.get position)) → carrier PUnit.unit goal)
    {goal : Pattern} :
    (derivationSignature K).Extension carrier PUnit.unit goal → carrier PUnit.unit goal
  | ⟨.byRule ruleInstance premises application, children⟩ =>
      build (.node ruleInstance premises application) children
  | ⟨.fact holds, _⟩ =>
      build (.computed (Classical.choose (AuthoredFamily.evaluate_complete holds))
        (Classical.choose_spec (AuthoredFamily.evaluate_complete holds)))
        fun position => position.elim0

/-- **Write a derivation as a certificate**: a rule node as a rule node, a
fact as a computed leaf that returns it. -/
noncomputable def write {goal : Pattern} (tree : (derivationSignature K).Proof goal) :
    (certificateSignature K).Proof goal :=
  Fix.fold (derivationSignature K)
    (carrier := fun _ goal => (certificateSignature K).Proof goal)
    (fun _ _ layer => writeLayer K (fun shape children => (certificateSignature K).node shape children)
      layer) PUnit.unit goal tree

/-- Write a derived rule as a certificate with holes. -/
noncomputable def writeContext {arity : Type} {holes : arity → Pattern} {goal : Pattern}
    (context : (derivationSignature K).Open holes goal) :
    (certificateSignature K).Open holes goal :=
  Free.fold (derivationSignature K)
    (fun _ _ hole => Free.pure (certificateSignature K) hole)
    { act := fun _ _ layer =>
        writeLayer K (fun shape children => Free.node (certificateSignature K) shape children)
          layer } PUnit.unit goal context

/-! ## Reading a certificate as a derivation -/

mutual

/-- A derivation of the generic checker, as a derivation of the signature. -/
def ofDerivation : {goal : Pattern} →
    Mettapedia.GSLT.LanguageDef.InferenceChecker.Derivation K.definition goal →
      (derivationSignature K).Proof goal
  | _, .byRule ruleInstance (premises := premises) application children =>
      (derivationSignature K).node (.byRule ruleInstance premises application)
        (ofDerivationList children)

/-- An ordered list of derivations, as a family over its positions. -/
def ofDerivationList : {premises : List Pattern} → DerivationList K.definition premises →
    (position : Fin premises.length) → (derivationSignature K).Proof (premises.get position)
  | _, .nil, position => position.elim0
  | _, .cons head _, ⟨0, _⟩ => ofDerivation head
  | _, .cons _ tail, ⟨index + 1, bound⟩ =>
      ofDerivationList tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩

end

/-- One layer of reading, into any family that has the nodes of derivations
and contains the derivations. -/
noncomputable def readLayer {carrier : PUnit.{1} → Pattern → Type}
    (build : ∀ {goal : Pattern} (shape : DerivationShape K goal),
      ((position : Fin shape.premises.length) →
        carrier PUnit.unit (shape.premises.get position)) → carrier PUnit.unit goal)
    (closed : ∀ {goal : Pattern}, (derivationSignature K).Proof goal → carrier PUnit.unit goal)
    {goal : Pattern} :
    (certificateSignature K).Extension carrier PUnit.unit goal → carrier PUnit.unit goal
  | ⟨.node ruleInstance premises application, children⟩ =>
      build (.byRule ruleInstance premises application) children
  | ⟨.computed _ returned, _⟩ =>
      build (.fact (AuthoredFamily.evaluate_sound returned)) fun position => position.elim0
  | ⟨.replay raw accepted, _⟩ => closed (ofDerivation K (derivationOf raw accepted))

/-- **Read a certificate as the derivation it stands for.** -/
noncomputable def read {goal : Pattern} (certificate : (certificateSignature K).Proof goal) :
    (derivationSignature K).Proof goal :=
  Fix.fold (certificateSignature K)
    (carrier := fun _ goal => (derivationSignature K).Proof goal)
    (fun _ _ layer => readLayer K
      (fun shape children => (derivationSignature K).node shape children) (fun tree => tree) layer)
    PUnit.unit goal certificate

/-- Read a certificate with holes as a derived rule. -/
noncomputable def readContext {arity : Type} {holes : arity → Pattern} {goal : Pattern}
    (context : (certificateSignature K).Open holes goal) :
    (derivationSignature K).Open holes goal :=
  Free.fold (certificateSignature K)
    (fun _ _ hole => Free.pure (derivationSignature K) hole)
    { act := fun _ _ layer =>
        readLayer K (fun shape children => Free.node (derivationSignature K) shape children)
          (fun tree => (derivationSignature K).close tree) layer } PUnit.unit goal context

/-- **Reading after writing is the identity.** -/
theorem read_write {goal : Pattern} (tree : (derivationSignature K).Proof goal) :
    read K (write K tree) = tree := by
  induction tree using RuleSignature.Proof.induction with
  | node shape children ih =>
      cases shape with
      | byRule ruleInstance premises application =>
          show (derivationSignature K).node (.byRule ruleInstance premises application)
            (fun position => read K (write K (children position))) = _
          exact congrArg _ (funext ih)
      | fact holds =>
          show (derivationSignature K).node (.fact _) (fun position => position.elim0) = _
          exact congrArg _ (funext fun position => position.elim0)

/-- Writing is injective: two derivations never share a certificate. -/
theorem write_injective {goal : Pattern} :
    Function.Injective (write K : (derivationSignature K).Proof goal → _) :=
  fun first second same => by
    have readSame := congrArg (read K) same
    rwa [read_write, read_write] at readSame

/-! ## The certificates are the accepted certificates of the checker -/

/-- One layer of erasure: forget the evidence at a node. -/
def eraseLayer {goal : Pattern} :
    (certificateSignature K).Extension (fun _ _ => CompactProof K.family.Leaf) PUnit.unit goal →
      CompactProof K.family.Leaf
  | ⟨.node ruleInstance _ _, children⟩ => .node ruleInstance (List.ofFn children)
  | ⟨.computed leaf _, _⟩ => .computed leaf
  | ⟨.replay raw _, _⟩ => .replay raw

/-- **The compact proof of a certificate**: what the checker is given. -/
noncomputable def erase {goal : Pattern} (certificate : (certificateSignature K).Proof goal) :
    CompactProof K.family.Leaf :=
  Fix.fold (certificateSignature K) (carrier := fun _ _ => CompactProof K.family.Leaf)
    (fun _ _ layer => eraseLayer K layer) PUnit.unit goal certificate

/-- Checking an ordered family of children is checking each. -/
theorem checkChildren_ofFn {Query : Type} (definition : ValidatedCalculusLanguageDef)
    (evaluate : Query → Option Pattern) :
    ∀ (premises : List Pattern) (proofs : Fin premises.length → CompactProof Query),
      checkChildren definition evaluate premises (List.ofFn proofs) = true ↔
        ∀ position, check definition evaluate (premises.get position) (proofs position) = true
  | [], proofs => by
      simp [checkChildren]
  | premise :: premises, proofs => by
      rw [List.ofFn_succ]
      simp only [checkChildren, Bool.and_eq_true, List.length_cons]
      rw [checkChildren_ofFn definition evaluate premises fun position => proofs position.succ,
        Fin.forall_fin_succ]
      rfl

/-- **The checker accepts the compact proof of every certificate.** -/
theorem check_erase {goal : Pattern} (certificate : (certificateSignature K).Proof goal) :
    check K.definition K.family.evaluate goal (erase K certificate) = true := by
  induction certificate using RuleSignature.Proof.induction with
  | node shape children ih =>
      cases shape with
      | node ruleInstance premises application =>
          show check K.definition K.family.evaluate _
            (.node ruleInstance (List.ofFn fun position => erase K (children position))) = true
          simp only [check, instantiateRule?_eq_some_iff_application.mpr application, decide_true,
            Bool.true_and]
          exact (checkChildren_ofFn K.definition K.family.evaluate premises _).mpr ih
      | computed leaf returned =>
          show check K.definition K.family.evaluate _ (.computed leaf) = true
          simp [check, returned]
      | replay raw accepted =>
          show check K.definition K.family.evaluate _ (.replay raw) = true
          simpa only [check] using accepted

mutual

/-- **Every accepted compact proof is the compact proof of a certificate.** -/
theorem exists_certificate {goal : Pattern} {proof : CompactProof K.family.Leaf}
    (accepted : check K.definition K.family.evaluate goal proof = true) :
    ∃ certificate : (certificateSignature K).Proof goal, erase K certificate = proof := by
  cases proof with
  | replay raw =>
      exact ⟨(certificateSignature K).node (.replay raw (by simpa only [check] using accepted))
        fun position => position.elim0, rfl⟩
  | computed leaf =>
      exact ⟨(certificateSignature K).node
        (.computed leaf (by simpa only [check, decide_eq_true_eq] using accepted))
        fun position => position.elim0, rfl⟩
  | node ruleInstance children =>
      simp only [check] at accepted
      cases application : instantiateRule? K.definition ruleInstance with
      | none => simp [application] at accepted
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [application, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨rfl, childrenAccepted⟩ := accepted
          obtain ⟨family, erased⟩ := exists_certificates childrenAccepted
          refine ⟨(certificateSignature K).node
            (.node ruleInstance premises (instantiateRule?_eq_some_iff_application.mp application))
            family, ?_⟩
          show CompactProof.node ruleInstance (List.ofFn fun position => erase K (family position)) =
            _
          rw [erased]
termination_by sizeOf proof
decreasing_by all_goals (subst_vars; simp only [CompactProof.node.sizeOf_spec]; omega)

theorem exists_certificates {premises : List Pattern} {proofs : List (CompactProof K.family.Leaf)}
    (accepted : checkChildren K.definition K.family.evaluate premises proofs = true) :
    ∃ family : (position : Fin premises.length) →
        (certificateSignature K).Proof (premises.get position),
      (List.ofFn fun position => erase K (family position)) = proofs := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => exact ⟨fun position => position.elim0, by simp⟩
      | cons _ _ => simp [checkChildren] at accepted
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkChildren] at accepted
      | cons proof proofs =>
          simp only [checkChildren, Bool.and_eq_true] at accepted
          obtain ⟨head, headErased⟩ := exists_certificate accepted.1
          obtain ⟨tail, tailErased⟩ := exists_certificates accepted.2
          refine ⟨fun position => Fin.cases
            (motive := fun position =>
              (certificateSignature K).Proof ((premise :: premises).get position))
            head tail position, ?_⟩
          rw [List.ofFn_succ]
          show (erase K head :: List.ofFn fun position => erase K (tail position)) = proof :: proofs
          rw [headErased, tailErased]
termination_by sizeOf proofs
decreasing_by all_goals (subst_vars; simp only [List.cons.sizeOf_spec]; omega)

end

/-- **A certificate is determined by its compact proof.** -/
theorem erase_injective {goal : Pattern} (first : (certificateSignature K).Proof goal) :
    ∀ second : (certificateSignature K).Proof goal, erase K first = erase K second →
      first = second := by
  induction first using RuleSignature.Proof.induction with
  | node shape children ih =>
      intro second same
      obtain ⟨shape', children', rfl⟩ := RuleSignature.Proof.exists_node _ second
      · cases shape with
          | node ruleInstance premises application =>
              cases shape' with
              | node ruleInstance' premises' application' =>
                  have erased : CompactProof.node ruleInstance
                        (List.ofFn fun position => erase K (children position)) =
                      CompactProof.node ruleInstance'
                        (List.ofFn fun position => erase K (children' position)) := same
                  obtain ⟨rfl, childrenErased⟩ := CompactProof.node.inj erased
                  obtain ⟨rfl, -⟩ := application.outputs_unique application'
                  have pointwise := List.ofFn_injective childrenErased
                  have equal : children = children' :=
                    funext fun position => ih position (children' position)
                      (congrFun pointwise position)
                  rw [equal]
              | computed leaf returned =>
                  have erased : CompactProof.node ruleInstance
                      (List.ofFn fun position => erase K (children position)) =
                        CompactProof.computed leaf := same
                  cases erased
              | replay raw accepted =>
                  have erased : CompactProof.node ruleInstance
                      (List.ofFn fun position => erase K (children position)) =
                        CompactProof.replay raw := same
                  cases erased
          | computed leaf returned =>
              cases shape' with
              | node ruleInstance' premises' application' =>
                  have erased : CompactProof.computed leaf = CompactProof.node ruleInstance'
                      (List.ofFn fun position => erase K (children' position)) := same
                  cases erased
              | computed leaf' returned' =>
                  have erased : CompactProof.computed leaf = CompactProof.computed leaf' := same
                  obtain rfl := CompactProof.computed.inj erased
                  have equal : children = children' := funext fun position => position.elim0
                  rw [equal]
              | replay raw accepted =>
                  have erased : CompactProof.computed leaf = CompactProof.replay raw := same
                  cases erased
          | replay raw accepted =>
              cases shape' with
              | node ruleInstance' premises' application' =>
                  have erased : CompactProof.replay raw = CompactProof.node ruleInstance'
                      (List.ofFn fun position => erase K (children' position)) := same
                  cases erased
              | computed leaf' returned' =>
                  have erased : CompactProof.replay raw = CompactProof.computed leaf' := same
                  cases erased
              | replay raw' accepted' =>
                  have erased : CompactProof.replay raw = CompactProof.replay raw' := same
                  obtain rfl := CompactProof.replay.inj erased
                  have equal : children = children' := funext fun position => position.elim0
                  rw [equal]

/-- The compact proofs that the specified checker accepts for a goal. -/
abbrev Accepted (goal : Pattern) : Type :=
  {proof : CompactProof K.family.Leaf //
    check K.definition K.family.evaluate goal proof = true}

/-- **The certificates of the signature are the accepted compact proofs.** -/
noncomputable def certificateEquiv (goal : Pattern) :
    (certificateSignature K).Proof goal ≃ Accepted K goal :=
  Equiv.ofBijective (fun certificate => ⟨erase K certificate, check_erase K certificate⟩)
    ⟨fun first second same => erase_injective K first second (congrArg Subtype.val same),
      fun accepted => by
        obtain ⟨certificate, erased⟩ := exists_certificate K accepted.2
        exact ⟨certificate, Subtype.ext erased⟩⟩

/-! ## Certificates compared by their reading -/

/-- **Two certificates count as the same when they stand for one
derivation.** -/
noncomputable def readCongruence : (certificateSignature K).ProofCongruence where
  setoid := fun _ =>
    ⟨fun first second => read K first = read K second,
      ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩⟩
  node := fun shape first second related => by
    show readLayer K (fun shape children => (derivationSignature K).node shape children)
        (fun tree => tree) ⟨shape, fun position => read K (first position)⟩ =
      readLayer K (fun shape children => (derivationSignature K).node shape children)
        (fun tree => tree) ⟨shape, fun position => read K (second position)⟩
    rw [funext related]

/-- **Certificates compared by their reading are in bijection with
derivations.** -/
noncomputable def readEquiv (goal : Pattern) :
    Quotient ((readCongruence K).setoid goal) ≃ (derivationSignature K).Proof goal where
  toFun := Quotient.lift (read K) fun _ _ same => same
  invFun := fun tree => Quotient.mk _ (write K tree)
  left_inv := by
    intro certificate
    induction certificate using Quotient.inductionOn with
    | h certificate => exact Quotient.sound (read_write K (read K certificate))
  right_inv := fun tree => read_write K tree

/-- **Reading is not injective on certificates.**  A certificate with a raw
replay tree at its root is not the certificate written from its reading, and
the two have the same reading. -/
theorem replay_ne_write_read {goal : Pattern} (raw : RawProof)
    (accepted : checkRaw K.definition goal raw = true) :
    let certificate := (certificateSignature K).node (.replay raw accepted)
      fun position => position.elim0
    write K (read K certificate) ≠ certificate ∧
      read K (write K (read K certificate)) = read K certificate := by
  refine ⟨fun same => ?_, read_write K _⟩
  have reading : read K ((certificateSignature K).node (.replay raw accepted)
      fun position => position.elim0) = ofDerivation K (derivationOf raw accepted) := rfl
  rw [reading] at same
  cases derivation : derivationOf raw accepted with
  | byRule ruleInstance application children =>
      rw [derivation] at same
      have shapes := congrArg (fun tree => (Fix.out (certificateSignature K) tree).1) same
      cases shapes

/-! ## The maps of theories -/

theorem write_fill {arity : Type} {holes : arity → Pattern} {goal : Pattern}
    (context : (derivationSignature K).Open holes goal)
    (filling : (index : arity) → (derivationSignature K).Proof (holes index)) :
    write K ((derivationSignature K).fill context filling) =
      (certificateSignature K).fill (writeContext K context) fun index =>
        write K (filling index) := by
  induction context using RuleSignature.Open.induction with
  | assume index => rfl
  | node shape children ih =>
      cases shape with
      | byRule ruleInstance premises application =>
          show (certificateSignature K).node (.node ruleInstance premises application)
              (fun position => write K ((derivationSignature K).fill (children position) filling)) =
            (certificateSignature K).node (.node ruleInstance premises application)
              (fun position => (certificateSignature K).fill (writeContext K (children position))
                fun index => write K (filling index))
          exact congrArg _ (funext ih)
      | fact holds =>
          show (certificateSignature K).node (.computed _ _) (fun position => position.elim0) =
            (certificateSignature K).node (.computed _ _) _
          exact congrArg _ (funext fun position => position.elim0)

theorem read_fill {arity : Type} {holes : arity → Pattern} {goal : Pattern}
    (context : (certificateSignature K).Open holes goal)
    (filling : (index : arity) → (certificateSignature K).Proof (holes index)) :
    read K ((certificateSignature K).fill context filling) =
      (derivationSignature K).fill (readContext K context) fun index =>
        read K (filling index) := by
  induction context using RuleSignature.Open.induction with
  | assume index => rfl
  | node shape children ih =>
      cases shape with
      | node ruleInstance premises application =>
          show (derivationSignature K).node (.byRule ruleInstance premises application)
              (fun position => read K ((certificateSignature K).fill (children position) filling)) =
            (derivationSignature K).node (.byRule ruleInstance premises application)
              (fun position => (derivationSignature K).fill (readContext K (children position))
                fun index => read K (filling index))
          exact congrArg _ (funext ih)
      | computed leaf returned =>
          show (derivationSignature K).node (.fact _) (fun position => position.elim0) =
            (derivationSignature K).node (.fact _) _
          exact congrArg _ (funext fun position => position.elim0)
      | replay raw accepted =>
          show ofDerivation K (derivationOf raw accepted) =
            (derivationSignature K).fill
              ((derivationSignature K).close (ofDerivation K (derivationOf raw accepted))) _
          exact ((derivationSignature K).fill_close _ _).symm

/-- **Writing, as a map of theories**: from the derivations of the calculus,
kept apart, to its certificates, compared by their reading. -/
noncomputable def writeMap :
    ContextMap ((derivationSignature K).proofTheory (RuleSignature.ProofCongruence.identity _))
      ((certificateSignature K).proofTheory (readCongruence K)) where
  interface := fun goal => goal
  term := fun tree => write K tree
  context := fun context => writeContext K context
  term_resp := fun same => congrArg (fun tree => read K (write K tree)) same
  equivariant := fun context filling => congrArg (read K) (write_fill K context filling)

/-- **Writing is hosting**: no two derivations become one certificate. -/
theorem writeMap_hosting : (writeMap K).Hosting := by
  rw [(derivationSignature K).hosting_iff_static _ (writeMap K) fun _ _ step => step]
  intro goal first second same
  have readSame : read K (write K first) = read K (write K second) := same
  exact (read_write K first).symm.trans (readSame.trans (read_write K second))

/-- A certificate with holes and the certificate written from its reading
stand for the same derivation, on certificates written from derivations. -/
theorem read_fill_writeContext {arity : Type} {holes : arity → Pattern} {goal : Pattern}
    (observer : (certificateSignature K).Open holes goal)
    (filling : (index : arity) → (derivationSignature K).Proof (holes index)) :
    read K ((certificateSignature K).fill (writeContext K (readContext K observer))
        fun index => write K (filling index)) =
      read K ((certificateSignature K).fill observer fun index => write K (filling index)) := by
  rw [← write_fill, read_write, read_fill]
  exact congrArg _ (funext fun index => (read_write K (filling index)).symm)

/-- **Writing is exhausting**: every certificate, and every certificate with
holes, stands for a derivation or a derived rule of the calculus. -/
theorem writeMap_exhausting : (writeMap K).Exhausting :=
  fun observer => ⟨readContext K observer, fun filling =>
    read_fill_writeContext K observer filling⟩

/-- **The certificates of an authored calculus host its derivations and add
nothing**, with the derivations kept apart. -/
theorem authoredCalculus_hosts_derivations :
    HostsExhaustively ((certificateSignature K).proofTheory (readCongruence K))
      ((derivationSignature K).proofTheory (RuleSignature.ProofCongruence.identity _)) :=
  ⟨writeMap K, writeMap_hosting K, writeMap_exhausting K⟩

/-- Writing, with the certificates compared by identity. -/
noncomputable def writeStrictMap :
    ContextMap ((derivationSignature K).proofTheory (RuleSignature.ProofCongruence.identity _))
      ((certificateSignature K).proofTheory (RuleSignature.ProofCongruence.identity _)) where
  interface := fun goal => goal
  term := fun tree => write K tree
  context := fun context => writeContext K context
  term_resp := fun same => congrArg (write K) same
  equivariant := fun context filling => write_fill K context filling

/-- Writing is hosting when certificates are compared by identity as well. -/
theorem writeStrictMap_hosting : (writeStrictMap K).Hosting := by
  rw [(derivationSignature K).hosting_iff_static _ (writeStrictMap K) fun _ _ step => step]
  exact fun same => write_injective K same

/-- **With certificates compared by identity the map is not exhausting**, as
soon as one raw replay tree is accepted: that certificate is written from no
derivation. -/
theorem writeStrictMap_not_exhausting {goal : Pattern} (raw : RawProof)
    (accepted : checkRaw K.definition goal raw = true) : ¬ (writeStrictMap K).Exhausting := by
  intro exhausting
  obtain ⟨preimage, written⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := goal) ((certificateSignature K).node (.replay raw accepted)
      fun position => position.elim0)
  have same : (certificateSignature K).node (.replay raw accepted)
      (fun position => position.elim0) = write K preimage := written
  have readSame : write K (read K ((certificateSignature K).node (.replay raw accepted)
      fun position => position.elim0)) = write K preimage :=
    (congrArg (fun certificate => write K (read K certificate)) same).trans
      (congrArg (write K) (read_write K preimage))
  exact (replay_ne_write_read K raw accepted).1 (readSame.trans same.symm)

#print axioms nonempty_tree_iff_derivable
#print axioms read_write
#print axioms check_erase
#print axioms exists_certificate
#print axioms erase_injective
#print axioms certificateEquiv
#print axioms readEquiv
#print axioms replay_ne_write_read
#print axioms authoredCalculus_hosts_derivations
#print axioms writeStrictMap_hosting
#print axioms writeStrictMap_not_exhausting

end Mettapedia.Logic.HostingStyles
