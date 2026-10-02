import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

/-!
# Observation relations at higher types, and why quotation is inadmissible

An *observation relation* is fixed by a relation `R` on processes and a choice
of equivalence at every ground sort.  It is lifted to products and function
types as a logical relation.  An operation is *admissible* when it is related
to itself: at a function type this says that it maps related arguments to
related results.

This module proves:

* admissible operations contain the identities and are closed under
  application, composition, pairing and projection (`admissible_app`,
  `admissible_comp`, `admissible_pair`, ...), and `R` is a congruence for the
  admissible operations from processes to processes;
* **quotation** (`quote_admissible_iff`): an operation from processes into a
  ground sort observed by equality is admissible exactly when `R` is contained
  in its kernel.  For an injective operation this means `R` is contained in
  equality (`quote_admissible_iff_of_injective`), so any relation that
  identifies two distinct processes makes it inadmissible
  (`quote_not_admissible`).

The kernel form matters when quotation is not injective.  With the reflective
equation `@(*n) = n`, quotation identifies `*(@0)` with `0`, so that pair can
never witness inadmissibility, while the pair `a!(*(@0))` and `a!(0)`, which
send the same name, has distinct quotations.  `QuoteWitness` checks both facts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.TypedObservation

universe u w

/-- Simple types over one process sort and a type `G` of ground sorts. -/
inductive Ty (G : Type u) : Type u where
  | proc : Ty G
  | ground (sort : G) : Ty G
  | prod (left right : Ty G) : Ty G
  | arrow (domain codomain : Ty G) : Ty G

variable {G : Type u}

namespace Ty

/-- The carrier of a type: processes, a carrier per ground sort, pairs and
functions. -/
def Denote (Proc : Type w) (Carrier : G → Type w) : Ty G → Type w
  | .proc => Proc
  | .ground sort => Carrier sort
  | .prod left right => Denote Proc Carrier left × Denote Proc Carrier right
  | .arrow domain codomain => Denote Proc Carrier domain → Denote Proc Carrier codomain

variable {Proc : Type w} {Carrier : G → Type w}

/-- **The observation relation.**  `R` at processes, the chosen equivalence at
ground sorts, componentwise at products, and the logical relation at function
types. -/
def ObsRel (R : Proc → Proc → Prop) (groundChoice : (sort : G) → Setoid (Carrier sort)) :
    (τ : Ty G) → τ.Denote Proc Carrier → τ.Denote Proc Carrier → Prop
  | .proc => R
  | .ground sort => (groundChoice sort).r
  | .prod left right => fun first second =>
      ObsRel R groundChoice left first.1 second.1 ∧ ObsRel R groundChoice right first.2 second.2
  | .arrow domain codomain => fun first second =>
      ∀ argument argument', ObsRel R groundChoice domain argument argument' →
        ObsRel R groundChoice codomain (first argument) (second argument')

end Ty

open Ty

variable {Proc : Type w} {Carrier : G → Type w}
variable (R : Proc → Proc → Prop) (groundChoice : (sort : G) → Setoid (Carrier sort))

/-- An operation is **admissible** when it is related to itself. -/
def Admissible (τ : Ty G) (operation : τ.Denote Proc Carrier) : Prop :=
  τ.ObsRel R groundChoice operation operation

/-- At a function type, admissibility is preservation of the observation
relation. -/
theorem admissible_arrow_iff (domain codomain : Ty G)
    (operation : (Ty.arrow domain codomain).Denote Proc Carrier) :
    Admissible R groundChoice (.arrow domain codomain) operation ↔
      ∀ argument argument', domain.ObsRel R groundChoice argument argument' →
        codomain.ObsRel R groundChoice (operation argument) (operation argument') :=
  Iff.rfl

/-- `R` is a congruence for every admissible operation on processes. -/
theorem admissible_proc_iff (operation : Proc → Proc) :
    Admissible (Carrier := Carrier) R groundChoice (.arrow .proc .proc) operation ↔
      ∀ first second, R first second → R (operation first) (operation second) :=
  Iff.rfl

/-! ## Closure of the admissible operations -/

theorem admissible_app {domain codomain : Ty G}
    {operation : (Ty.arrow domain codomain).Denote Proc Carrier}
    {argument : domain.Denote Proc Carrier}
    (admissibleOperation : Admissible R groundChoice (.arrow domain codomain) operation)
    (admissibleArgument : Admissible R groundChoice domain argument) :
    Admissible R groundChoice codomain (operation argument) :=
  admissibleOperation argument argument admissibleArgument

theorem admissible_id (τ : Ty G) :
    Admissible (Carrier := Carrier) R groundChoice (.arrow τ τ) (fun value => value) :=
  fun _ _ related => related

theorem admissible_comp {first second third : Ty G}
    {inner : (Ty.arrow first second).Denote Proc Carrier}
    {outer : (Ty.arrow second third).Denote Proc Carrier}
    (admissibleInner : Admissible R groundChoice (.arrow first second) inner)
    (admissibleOuter : Admissible R groundChoice (.arrow second third) outer) :
    Admissible R groundChoice (.arrow first third) (fun value => outer (inner value)) :=
  fun _ _ related => admissibleOuter _ _ (admissibleInner _ _ related)

theorem admissible_pair {left right : Ty G} {first : left.Denote Proc Carrier}
    {second : right.Denote Proc Carrier}
    (admissibleFirst : Admissible R groundChoice left first)
    (admissibleSecond : Admissible R groundChoice right second) :
    Admissible R groundChoice (.prod left right) (first, second) :=
  ⟨admissibleFirst, admissibleSecond⟩

theorem admissible_fst (left right : Ty G) :
    Admissible (Carrier := Carrier) R groundChoice (.arrow (.prod left right) left)
      (fun (pair : (Ty.prod left right).Denote Proc Carrier) => pair.1) :=
  fun _ _ related => related.1

theorem admissible_snd (left right : Ty G) :
    Admissible (Carrier := Carrier) R groundChoice (.arrow (.prod left right) right)
      (fun (pair : (Ty.prod left right).Denote Proc Carrier) => pair.2) :=
  fun _ _ related => related.2

/-! ## Quotation -/

/-- **Quotation (kernel form).**  An operation from processes into a ground
sort observed by equality is admissible exactly when every `R`-related pair
has equal images. -/
theorem quote_admissible_iff {nameSort : G}
    (equality : ∀ first second : Carrier nameSort,
      (groundChoice nameSort).r first second ↔ first = second)
    (quote : Proc → Carrier nameSort) :
    Admissible R groundChoice (.arrow .proc (.ground nameSort)) quote ↔
      ∀ first second, R first second → quote first = quote second := by
  constructor
  · intro admissible first second related
    exact (equality _ _).mp (admissible first second related)
  · intro kernel first second related
    exact (equality _ _).mpr (kernel first second related)

/-- **Quotation is inadmissible for every nontrivial relation** (injective
form): an injective operation into a sort observed by equality is admissible
exactly when `R` is contained in equality. -/
theorem quote_admissible_iff_of_injective {nameSort : G}
    (equality : ∀ first second : Carrier nameSort,
      (groundChoice nameSort).r first second ↔ first = second)
    {quote : Proc → Carrier nameSort} (injective : Function.Injective quote) :
    Admissible R groundChoice (.arrow .proc (.ground nameSort)) quote ↔
      ∀ first second, R first second → first = second := by
  rw [quote_admissible_iff R groundChoice equality]
  exact ⟨fun kernel first second related => injective (kernel first second related),
    fun contained first second related => congrArg quote (contained first second related)⟩

/-- A relation identifying two processes with distinct quotations makes
quotation inadmissible. -/
theorem quote_not_admissible {nameSort : G}
    (equality : ∀ first second : Carrier nameSort,
      (groundChoice nameSort).r first second ↔ first = second)
    (quote : Proc → Carrier nameSort) {first second : Proc} (related : R first second)
    (distinct : quote first ≠ quote second) :
    ¬ Admissible R groundChoice (.arrow .proc (.ground nameSort)) quote :=
  fun admissible => distinct ((quote_admissible_iff R groundChoice equality quote).mp
    admissible first second related)

/-- Equality on a ground sort, as a ground choice. -/
def equalityChoice (Carrier : G → Type w) (sort : G) : Setoid (Carrier sort) :=
  ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem equalityChoice_iff {sort : G} (first second : Carrier sort) :
    (equalityChoice Carrier sort).r first second ↔ first = second :=
  Iff.rfl

/-! ## Which pair witnesses the inadmissibility of quotation

Names are quoted processes, and the reflective equation `@(*n) = n` is built
into quotation: quoting a drop returns the dropped name.  Quotation is then not
injective, and the kernel form of `quote_admissible_iff` is the one that
applies. -/

namespace QuoteWitness

mutual
  /-- Processes: nil, the drop of a name, and output of a process on a name. -/
  inductive Process where
    | nil : Process
    | drop (name : Name) : Process
    | out (channel : Name) (payload : Process) : Process
  /-- Names: quoted processes. -/
  inductive Name where
    | quoted (process : Process) : Name
end

/-- Quotation modulo `@(*n) = n`. -/
def quote : Process → Name
  | .drop name => name
  | process => .quoted process

/-- The name `@0`. -/
def zeroName : Name := quote .nil

/-- `*(@0)`. -/
def dropZero : Process := .drop zeroName

/-- **The printed witness does not witness.**  `*(@0)` and `0` have the same
quotation, so no relation containing this pair is refuted by quotation. -/
theorem printed_witness_same_quote : quote dropZero = quote .nil := rfl

/-- An output sends the quotation of its payload. -/
def sentName : Process → Option Name
  | .out _ payload => some (quote payload)
  | _ => none

/-- **The corrected witness sends the same name.**  `a!(*(@0))` and `a!(0)` send
`@(*(@0)) = @0` on the same channel. -/
theorem corrected_witness_same_sent_name (channel : Name) :
    sentName (.out channel dropZero) = sentName (.out channel .nil) := rfl

/-- **And its quotations differ.** -/
theorem corrected_witness_distinct_quote (channel : Name) :
    quote (.out channel dropZero) ≠ quote (.out channel .nil) := by
  intro equal
  cases equal

/-- Hence every relation that identifies the corrected witness pair makes
quotation inadmissible when names are observed by equality. -/
theorem quote_not_admissible_of_corrected_witness
    (R : Process → Process → Prop) (channel : Name)
    (related : R (.out channel dropZero) (.out channel .nil)) :
    ¬ Admissible (Carrier := fun _ : Unit => Name) R (equalityChoice (fun _ : Unit => Name))
      (.arrow .proc (.ground ())) quote :=
  quote_not_admissible R (equalityChoice (fun _ : Unit => Name))
    (fun _ _ => Iff.rfl) quote related (corrected_witness_distinct_quote channel)

/-- The printed pair is compatible with admissibility: quotation preserves the
relation that identifies exactly that pair and nothing else. -/
theorem quote_admissible_for_printed_pair :
    Admissible (Carrier := fun _ : Unit => Name)
      (fun first second => first = second ∨
        (first = dropZero ∧ second = .nil) ∨ (first = .nil ∧ second = dropZero))
      (equalityChoice (fun _ : Unit => Name)) (.arrow .proc (.ground ())) quote := by
  intro first second related
  rcases related with equal | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact congrArg quote equal
  · exact printed_witness_same_quote
  · exact printed_witness_same_quote.symm

end QuoteWitness

end Mettapedia.GSLT.TypedObservation
