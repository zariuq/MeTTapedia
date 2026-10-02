import Mettapedia.Logic.Derivation
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Definitional conversion read back as propositional equality

A type theory is often presented twice over the same syntax.

* A **strong** variant has a rich definitional equality: besides the rules it
  shares with a weaker variant, it has further conversion rules (for example
  the unfolding of a recursor), and its conversion problems may diverge.
* A **carved** variant keeps only part of the definitional equality, so that
  its conversion can be decided, and states the removed equations as
  *propositional* equations, used through explicit transports.

`ConversionSplit` records this shape for any finitary rule system over
judgments `J`: the rules both variants share, the conversion rules of the
carved variant, the conversion rules only the strong variant has, and a
reading `reflect` of strong judgments in the carved variant (a definitional
equality is read as the corresponding propositional one; every other
judgment is read as itself).

**Reflection** (`ConversionSplit.reflection`): if every rule of the strong
variant is admissible in the carved variant after reading its premises and
conclusion, then every strong derivation becomes a carved derivation of the
read judgment.  The three obligations separate what each rule family needs:

* shared rules that consume a definitional equality (the conversion rule)
  need a *transport* along the propositional reading;
* the carved conversion rules need definitional equality to imply
  propositional equality in the carved variant;
* the strong-only conversion rules need a *propositional witness* of each of
  their equations in the carved variant.

The carved variant is a restriction of the strong one
(`ConversionSplit.restriction`), so on judgments that are read as themselves
the two variants derive the same judgments (`strong_iff_carved`).

**Certificates.**  A decidable interface to the carved rules turns replayable
derivation trees into an executable checker.  Its exact authority for the
carved variant (`carvedChecker_authority`) composes with reflection: on
judgments read as themselves, the strong judgment holds exactly when the
carved checker accepts some certificate (`strongChecker_authority`).  Neither
statement decides whether a certificate exists.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe u v

variable {J : Type u}

/-- The union of two finitary rule predicates. -/
def RuleUnion (first second : List J → J → Prop) : List J → J → Prop :=
  fun premises conclusion => first premises conclusion ∨ second premises conclusion

/-! ## Rule application with explicit premise lists -/

section Nodes

variable {rules : List J → J → Prop}

/-- A rule instance with no premises. -/
theorem derives₀ {conclusion : J} (rule : rules [] conclusion) : Derives rules conclusion :=
  Derives.node [] conclusion rule fun _ member => nomatch member

/-- A rule instance with one premise. -/
theorem derives₁ {first conclusion : J} (rule : rules [first] conclusion)
    (firstDerived : Derives rules first) : Derives rules conclusion :=
  Derives.node [first] conclusion rule fun premise member => by
    cases member with
    | head => exact firstDerived
    | tail _ rest => nomatch rest

/-- A rule instance with two premises. -/
theorem derives₂ {first second conclusion : J} (rule : rules [first, second] conclusion)
    (firstDerived : Derives rules first) (secondDerived : Derives rules second) :
    Derives rules conclusion :=
  Derives.node [first, second] conclusion rule fun premise member => by
    cases member with
    | head => exact firstDerived
    | tail _ rest =>
        cases rest with
        | head => exact secondDerived
        | tail _ rest' => nomatch rest'

end Nodes

/-- The first element of a list is a member. -/
theorem mem₀ {first : J} {rest : List J} : first ∈ first :: rest := .head rest

/-- The second element of a list is a member. -/
theorem mem₁ {first second : J} {rest : List J} : second ∈ first :: second :: rest :=
  .tail first (.head rest)

/-- A rule system whose conversion is split between a carved variant and a
strong variant over the same judgments. -/
structure ConversionSplit (J : Type u) where
  /-- Rules of both variants. -/
  shared : List J → J → Prop
  /-- Conversion rules of the carved variant (and hence of both). -/
  carvedConversion : List J → J → Prop
  /-- Conversion rules of the strong variant only. -/
  strongConversion : List J → J → Prop
  /-- The reading of strong judgments in the carved variant. -/
  reflect : J → J

namespace ConversionSplit

variable (split : ConversionSplit J)

/-- The carved variant: shared rules and the carved conversion rules. -/
def carved : List J → J → Prop := RuleUnion split.shared split.carvedConversion

/-- The strong variant: the carved variant and the strong-only conversion rules. -/
def strong : List J → J → Prop := RuleUnion split.carved split.strongConversion

/-- A rule family is *reflected* when each of its instances becomes admissible
in the carved variant once every premise and the conclusion are read by
`reflect`. -/
def Reflects (rules : List J → J → Prop) : Prop :=
  ∀ premises conclusion, rules premises conclusion →
    (∀ premise ∈ premises, Derives split.carved (split.reflect premise)) →
      Derives split.carved (split.reflect conclusion)

/-- **Reflection.**  When the shared rules, the carved conversion rules and
the strong-only conversion rules are all reflected, every derivation of the
strong variant yields a derivation of the read judgment in the carved
variant. -/
theorem reflection (sharedReflects : split.Reflects split.shared)
    (carvedReflects : split.Reflects split.carvedConversion)
    (strongReflects : split.Reflects split.strongConversion) {judgment : J}
    (derivation : Derives split.strong judgment) :
    Derives split.carved (split.reflect judgment) := by
  refine Derives.least (fun target => Derives split.carved (split.reflect target)) ?_ derivation
  intro premises conclusion rule subderivations
  rcases rule with (rule | rule) | rule
  · exact sharedReflects premises conclusion rule subderivations
  · exact carvedReflects premises conclusion rule subderivations
  · exact strongReflects premises conclusion rule subderivations

/-- **Restriction.**  Every carved derivation is a strong derivation. -/
theorem restriction {judgment : J} (derivation : Derives split.carved judgment) :
    Derives split.strong judgment :=
  Derives.mono (fun _ _ rule => Or.inl rule) derivation

/-- On a judgment read as itself, the strong and carved variants agree. -/
theorem strong_iff_carved (sharedReflects : split.Reflects split.shared)
    (carvedReflects : split.Reflects split.carvedConversion)
    (strongReflects : split.Reflects split.strongConversion) {judgment : J}
    (fixed : split.reflect judgment = judgment) :
    Derives split.strong judgment ↔ Derives split.carved judgment := by
  constructor
  · intro derivation
    have reflected := split.reflection sharedReflects carvedReflects strongReflects derivation
    rwa [fixed] at reflected
  · exact split.restriction

/-- A carved rule whose premises and conclusion are all read as themselves is
reflected by itself. -/
theorem reflects_of_fixed {rules : List J → J → Prop}
    (included : ∀ premises conclusion, rules premises conclusion →
      split.carved premises conclusion)
    (fixed : ∀ premises conclusion, rules premises conclusion →
      split.reflect conclusion = conclusion ∧ ∀ premise ∈ premises, split.reflect premise = premise) :
    split.Reflects rules := by
  intro premises conclusion rule subderivations
  obtain ⟨conclusionFixed, premisesFixed⟩ := fixed premises conclusion rule
  rw [conclusionFixed]
  refine Derives.node premises conclusion (included premises conclusion rule) ?_
  intro premise member
  have derived := subderivations premise member
  rwa [premisesFixed premise member] at derived

/-- Reflected rule families are closed under union. -/
theorem Reflects.union {first second : List J → J → Prop}
    (firstReflects : split.Reflects first) (secondReflects : split.Reflects second) :
    split.Reflects (RuleUnion first second) := by
  intro premises conclusion rule subderivations
  rcases rule with rule | rule
  · exact firstReflects premises conclusion rule subderivations
  · exact secondReflects premises conclusion rule subderivations

end ConversionSplit

/-! ## Certificates without choice -/

section Certificates

variable {rules : List J → J → Prop}

private theorem exists_children {W : Type v} (Good : Derivation J W → J → Prop) :
    ∀ premises : List J, (∀ premise ∈ premises, ∃ certificate, Good certificate premise) →
      ∃ children : List (Derivation J W), List.Forall₂ Good children premises
  | [], _ => ⟨[], .nil⟩
  | premise :: rest, found => by
      obtain ⟨head, headGood⟩ := found premise List.mem_cons_self
      obtain ⟨tail, tailGood⟩ := exists_children Good rest fun other member =>
        found other (List.mem_cons_of_mem premise member)
      exact ⟨head :: tail, .cons headGood tailGood⟩

private theorem ofFn_concl_of_forall₂ {interface : RuleWitness.{u, v} rules} :
    ∀ {children : List (Derivation J interface.W)} {premises : List J},
      List.Forall₂ (fun certificate premise =>
        certificate.valid interface = true ∧ certificate.concl = premise) children premises →
      (List.ofFn fun i : Fin children.length => (children.get i).concl) = premises ∧
        ∀ i : Fin children.length, (children.get i).valid interface = true
  | [], [], .nil => ⟨rfl, fun i => i.elim0⟩
  | child :: children, premise :: premises, .cons ⟨childValid, childConcl⟩ rest => by
      obtain ⟨concls, valids⟩ := ofFn_concl_of_forall₂ rest
      refine ⟨?_, ?_⟩
      · rw [List.ofFn_succ]
        exact congrArg₂ List.cons childConcl concls
      · intro i
        cases i using Fin.cases with
        | zero => exact childValid
        | succ i => exact valids i

/-- Certificate completeness for a rule interface, proved without choice:
every derivable judgment has a replayable certificate with that conclusion.
(`Derives.exists_derivation` states the same through `choose`.) -/
theorem exists_valid_certificate (interface : RuleWitness.{u, v} rules) :
    ∀ {judgment : J}, Derives rules judgment →
      ∃ certificate : Derivation J interface.W,
        certificate.valid interface = true ∧ certificate.concl = judgment := by
  intro judgment derivation
  induction derivation with
  | node premises conclusion rule _ ih =>
      obtain ⟨witness, witnessValid⟩ := interface.complete premises conclusion rule
      obtain ⟨children, good⟩ := exists_children
        (fun certificate premise =>
          certificate.valid interface = true ∧ certificate.concl = premise) premises ih
      obtain ⟨concls, valids⟩ := ofFn_concl_of_forall₂ good
      refine ⟨.node conclusion witness children.length children.get, ?_, rfl⟩
      simp only [Derivation.valid, Bool.and_eq_true, List.all_eq_true, List.forall_mem_ofFn_iff,
        id]
      exact ⟨by rw [concls]; exact witnessValid, valids⟩

end Certificates

/-! ## The carved checker and its authority for the strong variant -/

namespace ConversionSplit

variable (split : ConversionSplit J)

/-- The carved checker: replay a certificate against a decidable interface to
the carved rules and compare its conclusion with the claim. -/
def carvedChecker [DecidableEq J] (interface : RuleWitness.{u, v} split.carved) :
    Checker J (Derivation J interface.W) where
  check claim certificate := certificate.valid interface && decide (certificate.concl = claim)

/-- The carved checker is an exact authority for the carved variant. -/
theorem carvedChecker_authority [DecidableEq J] (interface : RuleWitness.{u, v} split.carved) :
    (split.carvedChecker interface).Authority (Derives split.carved) where
  sound := by
    intro claim certificate accepted
    simp only [carvedChecker, Bool.and_eq_true, decide_eq_true_eq] at accepted
    obtain ⟨valid, concl⟩ := accepted
    rw [← concl]
    exact Derivation.valid_sound interface certificate valid
  complete := by
    intro claim derivable
    obtain ⟨certificate, valid, concl⟩ := exists_valid_certificate interface derivable
    exact ⟨certificate, by simp [carvedChecker, valid, concl]⟩

/-- Judgments read as themselves. -/
abbrev Fixed : Type u := {judgment : J // split.reflect judgment = judgment}

/-- The carved checker restricted to judgments read as themselves. -/
def fixedChecker [DecidableEq J] (interface : RuleWitness.{u, v} split.carved) :
    Checker split.Fixed (Derivation J interface.W) where
  check claim certificate := (split.carvedChecker interface).check claim.1 certificate

/-- **The carved checker is an exact authority for the strong variant** on
judgments read as themselves: the strong judgment holds exactly when the
carved checker accepts some certificate.  This is reflection read at the
trust boundary. -/
theorem strongChecker_authority [DecidableEq J] (interface : RuleWitness.{u, v} split.carved)
    (sharedReflects : split.Reflects split.shared)
    (carvedReflects : split.Reflects split.carvedConversion)
    (strongReflects : split.Reflects split.strongConversion) :
    (split.fixedChecker interface).Authority (fun claim => Derives split.strong claim.1) where
  sound := by
    intro claim certificate accepted
    exact split.restriction ((split.carvedChecker_authority interface).sound claim.1 certificate
      accepted)
  complete := by
    intro claim derivable
    have carvedDerivable :=
      (split.strong_iff_carved sharedReflects carvedReflects strongReflects claim.2).mp derivable
    exact (split.carvedChecker_authority interface).complete claim.1 carvedDerivable

end ConversionSplit

end Mettapedia.TypeTheory.Unfolding
