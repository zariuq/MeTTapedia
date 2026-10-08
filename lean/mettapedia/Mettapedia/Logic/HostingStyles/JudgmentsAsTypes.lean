import Mettapedia.Logic.HostingStyles.ProofTheory
import Mettapedia.Logic.HostingStyles.FrameworkSemantics

/-!
# Judgments as types

The second way of hosting a proof system: one fixed framework, in which every
judgment becomes a type, every rule a constant, and every derivation a term.

For a finitary rule signature `P` the signature `finitary.signature` of the
framework has the judgments as base types and one constant for each rule
instance, whose argument types are the rule's premises and whose result is
its conclusion.  A derivation is encoded by applying constants
(`encodeTerm`), a derived rule by a term with a hole for each assumption
(`encodeContext`).  Both are folds: the terms of the framework carry an
algebra of the rule signature (`termAlgebra`).

## Adequacy

* **On canonical forms** (`canonicalEquiv`): encoding is a bijection between
  the derivations of a judgment and the canonical forms of its type.  It
  commutes with plugging derivations into assumptions (`encodeTerm_fill`).
  Derived rules are treated up to conversion below.
* **No two derivations are identified by conversion**
  (`encodeTerm_conv_iff`).  This is what confluence of the declared
  computation rule is used for in the literature: a conversion class holds at
  most one canonical form.  Here it is proved by a model: the derivations
  themselves model the signature, and the value of an encoded derivation is
  that derivation (`readback_encodeTerm`).
* **Every term of a judgment's type is convertible to the encoding of a
  derivation** (`conv_encodeTerm_readback`), canonical or not.  This is what
  termination of the declared computation rule and preservation of types are
  used for in the literature: every term has a canonical form of its type.
  Here it is proved by a logical relation between terms and their values
  (`Reading.fundamental`).  Neither confluence nor termination is assumed.
* Together (`adequacy`): the terms of a judgment's type, up to the declared
  conversion, are in bijection with the derivations of the judgment.

Encoding is not onto the terms themselves: a term with a redex is the
encoding of no derivation (`not_encodeTerm_of_step`).  It is onto them up to
conversion.

## As a map of theories

`encodingMap` is the encoding as a map from the theory of the rule signature,
with derivations kept apart, to the framework over the signature.  It is
hosting (`encodingMap_hosting`) and exhausting (`encodingMap_exhausting`):
the framework can state everything the proof system can, and nothing more up
to its conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Framework

/-- Transporting a family of values along a numbering of positions and
reading it back at numbered positions gives the family. -/
theorem piCongrLeft_comp {Index Position : Type} (family : Position → Type)
    (numbering : Index ≃ Position) (values : (position : Position) → family position) :
    Equiv.piCongrLeft family numbering (fun index => values (numbering index)) = values := by
  funext position
  obtain ⟨index, rfl⟩ := numbering.surjective position
  exact Equiv.piCongrLeft_apply_apply family numbering _ index

namespace RuleSignature

variable {J : Type} {P : RuleSignature J} (finitary : P.Finitary)

/-! ## Rules as constants -/

/-- **The signature of a proof system in the framework**: the base types are
the judgments, and each rule instance is a constant from its premises to its
conclusion. -/
abbrev Finitary.signature : Signature J where
  Const := Σ j : J, P.Shape PUnit.unit j
  arity := fun constant => finitary.arity constant.2
  argument := fun constant index =>
    .base (P.next constant.2 (finitary.position constant.2 index))
  result := fun constant => constant.1

/-- The holes of an indexed family of assumptions: one of each assumption's
type. -/
abbrev baseHoles {arity : Type} (assumptions : arity → J) : arity → Ty J :=
  fun index => .base (assumptions index)

variable {Hole : Type} {holes : Hole → Ty J}

/-- A rule applied to terms of its premises' types: a term of its
conclusion's type. -/
def Finitary.ruleTerm {context : List (Ty J)} {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) →
      Tm finitary.signature holes context (.base (P.next shape position))) :
    Tm finitary.signature holes context (.base j) :=
  Tm.conApp (signature := finitary.signature) ⟨j, shape⟩ fun index =>
    children (finitary.position shape index)

/-- **The terms of the framework carry an algebra of the rule signature.** -/
def Finitary.termAlgebra (holes : Hole → Ty J) :
    P.Algebra (fun _ j => Tm finitary.signature holes [] (.base j)) where
  act := fun _ _ layer => finitary.ruleTerm layer.1 layer.2

/-- **Encoding a derivation**: the fold into the algebra of terms. -/
noncomputable def Finitary.encodeTerm {j : J} (proof : P.Proof j) :
    Closed finitary.signature (.base j) :=
  Fix.fold P (finitary.termAlgebra noHoles).act PUnit.unit j proof

@[simp] theorem Finitary.encodeTerm_node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    finitary.encodeTerm (P.node shape children) =
      finitary.ruleTerm shape fun position => finitary.encodeTerm (children position) := rfl

/-- **Encoding a derived rule**: an assumption becomes a hole. -/
noncomputable def Finitary.encodeContext {arity : Type} {assumptions : arity → J} {j : J}
    (context : P.Open assumptions j) : Tm finitary.signature (baseHoles assumptions) [] (.base j) :=
  Free.fold P
    (fun _ _ hole => HoleAt.elim
      (motive := fun j => Tm finitary.signature (baseHoles assumptions) [] (.base j))
      (fun index => Tm.hole index) hole)
    (finitary.termAlgebra (baseHoles assumptions)) PUnit.unit j context

@[simp] theorem Finitary.encodeContext_assume {arity : Type} {assumptions : arity → J}
    (index : arity) :
    finitary.encodeContext (P.assume (holes := assumptions) index) = Tm.hole index := rfl

@[simp] theorem Finitary.encodeContext_node {arity : Type} {assumptions : arity → J} {j : J}
    (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Open assumptions (P.next shape position)) :
    finitary.encodeContext (Free.node P shape children) =
      finitary.ruleTerm shape fun position => finitary.encodeContext (children position) := rfl

/-- **Encoding is compositional**: the encoding of a derived rule with its
assumptions filled is the encoding of the rule with its holes filled by the
encodings. -/
theorem Finitary.encodeTerm_fill {arity : Type} {assumptions : arity → J} {j : J}
    (context : P.Open assumptions j) (filling : (index : arity) → P.Proof (assumptions index)) :
    finitary.encodeTerm (P.fill context filling) =
      (finitary.encodeContext context).fill fun index => finitary.encodeTerm (filling index) := by
  induction context using Open.induction with
  | assume index => exact (Tm.rename_closed _ _).symm
  | node shape children ih =>
      rw [fill_node, Finitary.encodeTerm_node, Finitary.encodeContext_node, Finitary.ruleTerm,
        Finitary.ruleTerm, Tm.fill_conApp]
      congr 1
      funext index
      exact ih _

/-! ## Reading terms back -/

/-- A reading of the framework over a rule signature: a carrier for each
judgment on which the rules act, a value for each hole, and a way to write a
carrier element as a term that commutes with the rules. -/
structure Reading (holes : Hole → Ty J) where
  Carrier : J → Type
  node : {j : J} → (shape : P.Shape PUnit.unit j) →
    ((position : P.Position shape) → Carrier (P.next shape position)) → Carrier j
  hole : (slot : Hole) → (holes slot).denote Carrier
  quote : {j : J} → Carrier j → Tm finitary.signature holes [] (.base j)
  quote_node : ∀ {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → Carrier (P.next shape position)),
    quote (node shape children) = finitary.ruleTerm shape fun position => quote (children position)

namespace Reading

variable {finitary} (reading : Reading finitary holes)

/-- The model of a reading: a constant acts as its rule. -/
def model : Model finitary.signature holes where
  Base := reading.Carrier
  const := fun constant values => reading.node constant.2
    (Equiv.piCongrLeft (fun position => reading.Carrier (P.next constant.2 position))
      (finitary.position constant.2) values)
  hole := reading.hole

/-- The value of a closed term. -/
def readback {type : Ty J} (term : Tm finitary.signature holes [] type) :
    type.denote reading.Carrier :=
  term.eval reading.model Env.empty

/-- Convertible terms have the same reading. -/
theorem readback_conv {type : Ty J} {first second : Tm finitary.signature holes [] type}
    (convertible : Conv first second) : reading.readback first = reading.readback second :=
  convertible.eval reading.model Env.empty

/-- A rule applied to terms is read as the rule applied to their readings. -/
theorem readback_ruleTerm {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) →
      Tm finitary.signature holes [] (.base (P.next shape position))) :
    reading.readback (finitary.ruleTerm shape children) =
      reading.node shape fun position => reading.readback (children position) := by
  rw [readback, Finitary.ruleTerm, Tm.eval_conApp]
  exact congrArg (reading.node shape)
    (piCongrLeft_comp _ _ fun position => reading.readback (children position))

/-- **The relation between a term and a value**: at a judgment, the term is
convertible to the value written as a term; at a function type, related
arguments give related results. -/
def Related : (type : Ty J) → Tm finitary.signature holes [] type →
    type.denote reading.Carrier → Prop
  | .base _, term, value => Conv term (reading.quote value)
  | .arrow domain codomain, term, value =>
      ∀ argument argumentValue, Related domain argument argumentValue →
        Related codomain (.app term argument) (value.1 argumentValue)

/-- The relation is closed under conversion of the term. -/
theorem Related.conv : ∀ (type : Ty J) {first second : Tm finitary.signature holes [] type}
    {value : type.denote reading.Carrier}, Conv first second →
      reading.Related type second value → reading.Related type first value
  | .base _, _, _, _, convertible, related => .trans _ _ _ convertible related
  | .arrow _ codomain, _, _, _, convertible, related => fun argument argumentValue arguments =>
      Related.conv codomain (Conv.app convertible (.refl _))
        (related argument argumentValue arguments)

/-- A head is related to a curried operation when applying it to related
arguments gives a term convertible to the result written as a term. -/
theorem related_curry : ∀ (count : Nat) (arguments : Fin count → Ty J) (result : J)
    (head : Tm finitary.signature holes [] (curried count arguments result))
    (operation : ((index : Fin count) → (arguments index).denote reading.Carrier) →
      reading.Carrier result),
    (∀ (values : (index : Fin count) → Tm finitary.signature holes [] (arguments index))
      (denotations : (index : Fin count) → (arguments index).denote reading.Carrier),
      (∀ index, reading.Related (arguments index) (values index) (denotations index)) →
        Conv (Tm.applyArgs count arguments result head values)
          (reading.quote (operation denotations))) →
      reading.Related (curried count arguments result) head
        (curry reading.Carrier count arguments result operation)
  | 0, _, _, head, operation, applied => by
      have same := applied (fun index => index.elim0) (fun index => index.elim0)
        (fun index => index.elim0)
      exact same
  | count + 1, arguments, result, head, operation, applied => by
      intro argument argumentValue related
      refine related_curry count (fun index => arguments index.succ) result
        (.app head argument) _ ?_
      intro values denotations each
      have same := applied (Fin.cons (α := fun index => Tm finitary.signature holes [] (arguments index))
          argument values)
        (Fin.cons (α := fun index => (arguments index).denote reading.Carrier)
          argumentValue denotations)
        (fun index => by
          refine Fin.cases ?_ (fun index => ?_) index
          · exact related
          · exact each index)
      exact same

/-- **Every term is related to its value**, under a substitution of related
terms for its variables. -/
theorem fundamental
    (holesRelated : ∀ slot, reading.Related (holes slot) (.hole slot) (reading.hole slot))
    {context : List (Ty J)} {type : Ty J} (term : Tm finitary.signature holes context type) :
    ∀ (substitution : Subst finitary.signature holes context [])
      (environment : Env reading.Carrier context),
      (∀ type name, reading.Related type (substitution type name) (environment type name)) →
        reading.Related type (term.subst substitution) (term.eval reading.model environment) := by
  induction term with
  | var name => exact fun _ _ related => related _ name
  | con constant =>
      intro substitution environment _
      obtain ⟨j, shape⟩ := constant
      refine reading.related_curry _ _ _ _ _ ?_
      intro values denotations each
      have written : reading.quote (reading.model.const ⟨j, shape⟩ denotations) =
          Tm.conApp (signature := finitary.signature) ⟨j, shape⟩ fun index =>
            reading.quote (j := P.next shape (finitary.position shape index))
              (denotations index) := by
        change reading.quote (reading.node shape _) = _
        rw [reading.quote_node, Finitary.ruleTerm]
        congr 1
        funext index
        exact congrArg reading.quote (Equiv.piCongrLeft_apply_apply _ _ _ index)
      rw [written]
      exact Conv.conApp _ each
  | hole slot => exact fun _ _ _ => holesRelated slot
  | lam body ih =>
      intro substitution environment related argument argumentValue arguments
      refine Related.conv reading _ (.rel _ _ (.beta _ _)) ?_
      rw [Tm.subst_lift_inst]
      refine ih _ _ ?_
      intro type name
      cases name with
      | zero => exact arguments
      | succ name => exact related _ name
  | app function argument ihFunction ihArgument =>
      intro substitution environment related
      exact ihFunction substitution environment related _ _
        (ihArgument substitution environment related)

/-- **Every closed term of a judgment's type is convertible to its reading,
written as a term.** -/
theorem conv_quote_readback
    (holesRelated : ∀ slot, reading.Related (holes slot) (.hole slot) (reading.hole slot))
    {j : J} (term : Tm finitary.signature holes [] (.base j)) :
    Conv term (reading.quote (reading.readback term)) := by
  have related := reading.fundamental holesRelated term (fun _ name => nomatch name) Env.empty
    (fun _ name => nomatch name)
  rwa [Tm.subst_closed] at related

end Reading

/-! ## The two readings: derivations, and derived rules -/

/-- Closed terms are read as derivations. -/
noncomputable def Finitary.proofReading : Reading finitary (noHoles (B := J)) where
  Carrier := P.Proof
  node := P.node
  hole := fun slot => nomatch slot
  quote := finitary.encodeTerm
  quote_node := fun _ _ => rfl

/-- Terms with a hole for each assumption are read as derived rules. -/
noncomputable def Finitary.openReading {arity : Type} (assumptions : arity → J) :
    Reading finitary (baseHoles assumptions) where
  Carrier := P.Open assumptions
  node := fun shape children => Free.node P shape children
  hole := fun slot => P.assume slot
  quote := finitary.encodeContext
  quote_node := fun _ _ => rfl

/-- **The derivation a closed term of a judgment's type stands for.**  It is
defined for every term, canonical or not. -/
noncomputable def Finitary.readback {j : J} (term : Closed finitary.signature (.base j)) :
    P.Proof j :=
  finitary.proofReading.readback term

/-- The derived rule a term with holes stands for. -/
noncomputable def Finitary.readbackContext {arity : Type} {assumptions : arity → J} {j : J}
    (term : Tm finitary.signature (baseHoles assumptions) [] (.base j)) : P.Open assumptions j :=
  (finitary.openReading assumptions).readback term

/-- **An encoded derivation is read back as itself.** -/
theorem Finitary.readback_encodeTerm {j : J} (proof : P.Proof j) :
    finitary.readback (finitary.encodeTerm proof) = proof := by
  induction proof using Proof.induction with
  | node shape children ih =>
      rw [Finitary.encodeTerm_node, Finitary.readback, Reading.readback_ruleTerm]
      exact congrArg (P.node shape) (funext ih)

/-- An encoded derived rule is read back as itself. -/
theorem Finitary.readbackContext_encodeContext {arity : Type} {assumptions : arity → J} {j : J}
    (context : P.Open assumptions j) :
    finitary.readbackContext (finitary.encodeContext context) = context := by
  induction context using Open.induction with
  | assume index => rfl
  | node shape children ih =>
      rw [Finitary.encodeContext_node, Finitary.readbackContext, Reading.readback_ruleTerm]
      exact congrArg (Free.node P shape) (funext ih)

/-- **Conversion identifies no two derivations.** -/
theorem Finitary.encodeTerm_conv_iff {j : J} (first second : P.Proof j) :
    Conv (finitary.encodeTerm first) (finitary.encodeTerm second) ↔ first = second := by
  constructor
  · intro convertible
    have same := finitary.proofReading.readback_conv convertible
    rwa [← Finitary.readback, ← Finitary.readback, Finitary.readback_encodeTerm,
      Finitary.readback_encodeTerm] at same
  · rintro rfl
    exact .refl _

/-- **Every term of a judgment's type is convertible to the encoding of the
derivation it stands for.** -/
theorem Finitary.conv_encodeTerm_readback {j : J} (term : Closed finitary.signature (.base j)) :
    Conv term (finitary.encodeTerm (finitary.readback term)) :=
  finitary.proofReading.conv_quote_readback (fun slot => nomatch slot) term

/-- Every term with holes is convertible to the encoding of the derived rule
it stands for. -/
theorem Finitary.conv_encodeContext_readback {arity : Type} {assumptions : arity → J} {j : J}
    (term : Tm finitary.signature (baseHoles assumptions) [] (.base j)) :
    Conv term (finitary.encodeContext (finitary.readbackContext term)) :=
  (finitary.openReading assumptions).conv_quote_readback (fun _ => .refl _) term

/-- **Adequacy up to the declared conversion**: the terms of a judgment's
type, up to conversion, are the derivations of the judgment. -/
noncomputable def Finitary.adequacy (j : J) :
    Quot (Conv (signature := finitary.signature) (holes := noHoles (B := J)) (context := [])
      (type := .base j)) ≃ P.Proof j where
  toFun := Quot.lift finitary.readback fun _ _ convertible =>
    finitary.proofReading.readback_conv convertible
  invFun := fun proof => Quot.mk _ (finitary.encodeTerm proof)
  left_inv := by
    rintro ⟨term⟩
    exact Quot.sound (.symm _ _ (finitary.conv_encodeTerm_readback term))
  right_inv := fun proof => finitary.readback_encodeTerm proof

/-! ## Canonical forms -/

/-- A derivation as a canonical form. -/
noncomputable def Finitary.encodeNf {j : J} (proof : P.Proof j) :
    Nf finitary.signature (noHoles (B := J)) [] (.base j) :=
  Fix.fold P (carrier := fun _ j => Nf finitary.signature (noHoles (B := J)) [] (.base j))
    (fun _ j layer => Nf.con (signature := finitary.signature) ⟨j, layer.1⟩ fun index =>
      layer.2 (finitary.position layer.1 index))
    PUnit.unit j proof

@[simp] theorem Finitary.encodeNf_node {j : J} (shape : P.Shape PUnit.unit j)
    (children : (position : P.Position shape) → P.Proof (P.next shape position)) :
    finitary.encodeNf (P.node shape children) =
      Nf.con (signature := finitary.signature) ⟨j, shape⟩ fun index =>
        finitary.encodeNf (children (finitary.position shape index)) := rfl

/-- The canonical form of a derivation, as a term, is its encoding. -/
theorem Finitary.toTm_encodeNf {j : J} (proof : P.Proof j) :
    (finitary.encodeNf proof).toTm = finitary.encodeTerm proof := by
  induction proof using Proof.induction with
  | node shape children ih =>
      rw [Finitary.encodeNf_node, Nf.toTm, Finitary.encodeTerm_node, Finitary.ruleTerm]
      congr 1
      funext index
      exact ih _

/-- Distinct derivations have distinct canonical forms. -/
theorem Finitary.encodeNf_injective {j : J} :
    Function.Injective (finitary.encodeNf (j := j)) := by
  intro first second same
  have terms := congrArg Nf.toTm same
  rw [Finitary.toTm_encodeNf, Finitary.toTm_encodeNf] at terms
  exact (finitary.encodeTerm_conv_iff first second).mp (Conv.of_eq terms)

/-- Every canonical form of a judgment's type, in the empty context, is the
canonical form of a derivation. -/
theorem Finitary.encodeNf_reaches {context : List (Ty J)} {type : Ty J}
    (normal : Nf finitary.signature (noHoles (B := J)) context type) : context = [] →
      ∀ j : J, type = .base j → ∃ proof : P.Proof j, HEq (finitary.encodeNf proof) normal := by
  refine Nf.rec
    (motive_1 := fun context type normal => context = [] → ∀ j : J, type = .base j →
      ∃ proof : P.Proof j, HEq (finitary.encodeNf proof) normal)
    (motive_2 := fun _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ normal
  · intro context domain codomain body _ _ j same
    exact nomatch same
  · intro context constant arguments ih closed j same
    subst closed
    cases same
    choose proofs reached using fun index => ih index rfl _ rfl
    obtain ⟨j, shape⟩ := constant
    refine ⟨P.node shape (Equiv.piCongrLeft (fun position => P.Proof (P.next shape position))
      (finitary.position shape) proofs), heq_of_eq ?_⟩
    rw [Finitary.encodeNf_node]
    congr 1
    funext index
    rw [Equiv.piCongrLeft_apply_apply]
    exact eq_of_heq (reached index)
  · intro context type atom name spine _ closed j same
    subst closed
    exact nomatch name
  · intro context atom slot spine _ closed j same
    exact nomatch slot
  · intros
    trivial
  · intros
    trivial

theorem Finitary.encodeNf_surjective {j : J} :
    Function.Surjective (finitary.encodeNf (j := j)) := by
  intro normal
  obtain ⟨proof, reached⟩ := finitary.encodeNf_reaches normal rfl j rfl
  exact ⟨proof, eq_of_heq reached⟩

/-- **Adequacy on canonical forms**: the derivations of a judgment are the
canonical forms of its type. -/
noncomputable def Finitary.canonicalEquiv (j : J) :
    P.Proof j ≃ Nf finitary.signature (noHoles (B := J)) [] (.base j) :=
  Equiv.ofBijective finitary.encodeNf ⟨finitary.encodeNf_injective, finitary.encodeNf_surjective⟩

/-- An encoded derivation has no step. -/
theorem Finitary.encodeTerm_normal {j : J} (proof : P.Proof j) :
    Normal (finitary.encodeTerm proof) := by
  rw [← Finitary.toTm_encodeNf]
  exact Nf.toTm_normal _

/-- **A term with a step is the encoding of no derivation.**  Encoding
reaches the canonical forms, not the terms. -/
theorem Finitary.not_encodeTerm_of_step {j : J} {term next : Closed finitary.signature (.base j)}
    (step : Step term next) (proof : P.Proof j) : finitary.encodeTerm proof ≠ term := by
  rintro rfl
  exact finitary.encodeTerm_normal proof next step

/-- For every derivation there is a different term of the same type that is
convertible to its encoding: a redex that computes to it. -/
theorem Finitary.exists_noncanonical {j : J} (proof : P.Proof j) :
    ∃ term : Closed finitary.signature (.base j),
      (∀ other, finitary.encodeTerm other ≠ term) ∧ Conv term (finitary.encodeTerm proof) :=
  ⟨.app (.lam (.var .zero)) (finitary.encodeTerm proof),
    finitary.not_encodeTerm_of_step (.beta _ _), .rel _ _ (.beta _ _)⟩

/-! ## The encoding as a map of theories -/

/-- **The judgments-as-types encoding, as a map of theories.** -/
noncomputable def Finitary.encodingMap :
    ContextMap (P.proofTheory (ProofCongruence.identity P)) (frameworkTheory finitary.signature) where
  interface := fun j => .base j
  term := fun proof => finitary.encodeTerm proof
  context := fun context => finitary.encodeContext context
  term_resp := fun same => by
    have equal := same
    subst equal
    exact .refl _
  equivariant := fun context filling =>
    Conv.of_eq (finitary.encodeTerm_fill context filling)

/-- **The encoding is hosting**: the framework keeps every derivation
apart. -/
theorem Finitary.encodingMap_hosting : finitary.encodingMap.Hosting := by
  rw [P.hosting_iff_static _ _ (fun _ _ step => step)]
  intro j first second convertible
  exact (finitary.encodeTerm_conv_iff first second).mp convertible

/-- **The encoding is exhausting**: up to the declared conversion, every
term of the framework between judgments is the encoding of a derived rule. -/
theorem Finitary.encodingMap_exhausting : finitary.encodingMap.Exhausting := by
  intro arity assumptions result observer
  refine ⟨finitary.readbackContext observer, fun filling => ?_⟩
  exact Conv.map (fun term => term.fill _) (fun _ _ step => step.fill _)
    (.symm _ _ (finitary.conv_encodeContext_readback observer))

end RuleSignature

#print axioms RuleSignature.Reading.fundamental
#print axioms RuleSignature.Finitary.encodeTerm_conv_iff
#print axioms RuleSignature.Finitary.conv_encodeTerm_readback
#print axioms RuleSignature.Finitary.adequacy
#print axioms RuleSignature.Finitary.canonicalEquiv
#print axioms RuleSignature.Finitary.exists_noncanonical
#print axioms RuleSignature.Finitary.encodingMap_hosting
#print axioms RuleSignature.Finitary.encodingMap_exhausting

end Mettapedia.Logic.HostingStyles
