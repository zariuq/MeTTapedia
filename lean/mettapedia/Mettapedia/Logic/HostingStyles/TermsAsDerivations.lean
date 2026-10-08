import Mettapedia.Logic.HostingStyles.ReducingProofTheories
import Mettapedia.GSLT.Dedukti.Presentation

/-!
# A calculus as a member of the common class

A calculus is a rule signature through its formation rules: one judgment,
"is a term", and one rule for each term former, with the immediate subterms
as premises.  A derivation is a term, a derived rule is a term with holes,
and the steps of the calculus are a reduction on the derivations.

This is done here for the terms of the λΠ-calculus modulo.

* `termSignature`: the formation rules.  Its derivations are the terms
  (`toTerm`, `ofTerm`, inverse to each other) and its derived rules are the
  terms with holes (`toContext`, `ofContext`).
* `termTheory T`: the signature read at the steps of a theory `T`.  It is in
  the common class (`termTheory_reducing`).
* It is the running presentation of `T`: the map to `rewritingTheory T` is
  hosting and exhausting (`formedMap_hosting`, `formedMap_exhausting`), and the
  map back is hosting (`unformedMap_hosting`).

## Both kinds in one host

`threeKinds T` is a family of three members of the class: the worked logic,
the worked logic with the contraction of `K`, and the calculus of `T`.  Their
union hosts each (`threeKinds_hostsEvery`), and through it the running
presentation of `T` (`threeKinds_hosts_rewritingTheory`).

## Separation on the computational member

Forgetting the steps of a calculus is not hosting as soon as it has one
(`forgetSteps_not_hosting`): the syntax alone, which is a proof system in the
sense of `ProofTheory`, does not host the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti (Theory Step rewritingTheory TermContext)

/-! ## The formation rules -/

/-- The term formers of the λΠ terms. -/
inductive TermFormer : Type where
  | var (index : Nat)
  | srt (sort : LF.Srt)
  | con (name : String)
  | pi
  | lam
  | app

/-- The number of immediate subterms. -/
def TermFormer.arity : TermFormer → Nat
  | .var _ => 0
  | .srt _ => 0
  | .con _ => 0
  | .pi => 2
  | .lam => 2
  | .app => 2

/-- **The formation rules of the λΠ terms**: one judgment, one rule for each
term former. -/
def termSignature : RuleSignature Unit where
  Shape := fun _ _ => TermFormer
  Position := fun former => Fin former.arity
  next := fun _ _ => ()

/-- A family over two positions. -/
def two {α : Type} (first second : α) : Fin 2 → α :=
  fun position => Fin.cases first (fun _ => second) position

theorem two_eta {α : Type} (family : Fin 2 → α) : two (family 0) (family 1) = family := by
  funext position
  refine Fin.cases rfl (fun rest => ?_) position
  have only : rest = 0 := Subsingleton.elim _ _
  rw [only]
  rfl

theorem comp_two {α β : Type} (function : α → β) (first second : α) :
    (fun position => function (two first second position)) = two (function first)
      (function second) := by
  funext position
  refine Fin.cases rfl (fun _ => rfl) position

/-- One layer of a term with holes. -/
def formLayer {slots : Type} {judgment : Unit} :
    termSignature.Extension (fun _ _ => TermContext slots) PUnit.unit judgment → TermContext slots
  | ⟨.var index, _⟩ => .var index
  | ⟨.srt sort, _⟩ => .srt sort
  | ⟨.con name, _⟩ => .con name
  | ⟨.pi, parts⟩ => .pi (parts (0 : Fin 2)) (parts (1 : Fin 2))
  | ⟨.lam, parts⟩ => .lam (parts (0 : Fin 2)) (parts (1 : Fin 2))
  | ⟨.app, parts⟩ => .app (parts (0 : Fin 2)) (parts (1 : Fin 2))

/-- **A derived rule of the formation rules is a term with holes.** -/
noncomputable def toContext {arity : Type} {holes : arity → Unit} {judgment : Unit}
    (context : termSignature.Open holes judgment) : TermContext arity :=
  Free.fold termSignature (fun _ _ hole => TermContext.hole hole.1)
    { act := fun _ _ layer => formLayer layer } PUnit.unit judgment context

/-- **A derivation of the formation rules is a term.** -/
noncomputable def toTerm {judgment : Unit} (formed : termSignature.Proof judgment) : LF.Term :=
  TermContext.fill (fun impossible : Empty => impossible.elim)
    (Fix.fold termSignature (carrier := fun _ _ => TermContext Empty)
      (fun _ _ layer => formLayer layer) PUnit.unit judgment formed)

/-- A term, as a derivation of the formation rules. -/
def ofTerm : LF.Term → termSignature.Proof ()
  | .var index => termSignature.node (.var index) fun position => position.elim0
  | .srt sort => termSignature.node (.srt sort) fun position => position.elim0
  | .con name => termSignature.node (.con name) fun position => position.elim0
  | .pi domain body => termSignature.node .pi (two (ofTerm domain) (ofTerm body))
  | .lam domain body => termSignature.node .lam (two (ofTerm domain) (ofTerm body))
  | .app function argument => termSignature.node .app (two (ofTerm function) (ofTerm argument))

/-- A term with holes, as a derived rule of the formation rules. -/
def ofContext {arity : Type} : TermContext arity → termSignature.Open (fun _ : arity => ()) ()
  | .hole slot => termSignature.assume (holes := fun _ : arity => ()) slot
  | .var index => Free.node termSignature (.var index) fun position => position.elim0
  | .srt sort => Free.node termSignature (.srt sort) fun position => position.elim0
  | .con name => Free.node termSignature (.con name) fun position => position.elim0
  | .pi domain body => Free.node termSignature .pi (two (ofContext domain) (ofContext body))
  | .lam domain body => Free.node termSignature .lam (two (ofContext domain) (ofContext body))
  | .app function argument =>
      Free.node termSignature .app (two (ofContext function) (ofContext argument))

theorem toTerm_ofTerm (term : LF.Term) : toTerm (ofTerm term) = term := by
  induction term with
  | var index => rfl
  | srt sort => rfl
  | con name => rfl
  | pi domain body ihDomain ihBody =>
      show LF.Term.pi (toTerm (ofTerm domain)) (toTerm (ofTerm body)) = _
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      show LF.Term.lam (toTerm (ofTerm domain)) (toTerm (ofTerm body)) = _
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      show LF.Term.app (toTerm (ofTerm function)) (toTerm (ofTerm argument)) = _
      rw [ihFunction, ihArgument]

theorem ofTerm_toTerm {judgment : Unit} (formed : termSignature.Proof judgment) :
    ofTerm (toTerm formed) = formed := by
  induction formed using RuleSignature.Proof.induction with
  | node former parts ih =>
      cases former with
      | var index =>
          show termSignature.node (.var index) (fun position => position.elim0) = _
          exact congrArg _ (funext fun position => position.elim0)
      | srt sort =>
          show termSignature.node (.srt sort) (fun position => position.elim0) = _
          exact congrArg _ (funext fun position => position.elim0)
      | con name =>
          show termSignature.node (.con name) (fun position => position.elim0) = _
          exact congrArg _ (funext fun position => position.elim0)
      | pi =>
          exact congrArg (termSignature.node (j := ()) TermFormer.pi)
            ((congrArg₂ two (ih (0 : Fin 2)) (ih (1 : Fin 2))).trans
              (two_eta (α := termSignature.Proof ()) parts))
      | lam =>
          exact congrArg (termSignature.node (j := ()) TermFormer.lam)
            ((congrArg₂ two (ih (0 : Fin 2)) (ih (1 : Fin 2))).trans
              (two_eta (α := termSignature.Proof ()) parts))
      | app =>
          exact congrArg (termSignature.node (j := ()) TermFormer.app)
            ((congrArg₂ two (ih (0 : Fin 2)) (ih (1 : Fin 2))).trans
              (two_eta (α := termSignature.Proof ()) parts))

theorem toTerm_injective : Function.Injective (toTerm : termSignature.Proof () → LF.Term) :=
  fun first second same => by
    rw [← ofTerm_toTerm first, ← ofTerm_toTerm second, same]

theorem ofTerm_injective : Function.Injective ofTerm :=
  fun first second same => by
    rw [← toTerm_ofTerm first, ← toTerm_ofTerm second, same]

/-- Reading commutes with filling. -/
theorem toTerm_fill {arity : Type} {holes : arity → Unit} {judgment : Unit}
    (context : termSignature.Open holes judgment)
    (filling : (index : arity) → termSignature.Proof (holes index)) :
    toTerm (termSignature.fill context filling) =
      (toContext context).fill fun index => toTerm (filling index) := by
  induction context using RuleSignature.Open.induction with
  | assume index => rfl
  | node former parts ih =>
      cases former with
      | var index => rfl
      | srt sort => rfl
      | con name => rfl
      | pi =>
          show LF.Term.pi (toTerm (termSignature.fill (parts (0 : Fin 2)) filling))
              (toTerm (termSignature.fill (parts (1 : Fin 2)) filling)) =
            LF.Term.pi ((toContext (parts (0 : Fin 2))).fill fun index => toTerm (filling index))
              ((toContext (parts (1 : Fin 2))).fill fun index => toTerm (filling index))
          rw [ih (0 : Fin 2), ih (1 : Fin 2)]
      | lam =>
          show LF.Term.lam (toTerm (termSignature.fill (parts (0 : Fin 2)) filling))
              (toTerm (termSignature.fill (parts (1 : Fin 2)) filling)) =
            LF.Term.lam ((toContext (parts (0 : Fin 2))).fill fun index => toTerm (filling index))
              ((toContext (parts (1 : Fin 2))).fill fun index => toTerm (filling index))
          rw [ih (0 : Fin 2), ih (1 : Fin 2)]
      | app =>
          show LF.Term.app (toTerm (termSignature.fill (parts (0 : Fin 2)) filling))
              (toTerm (termSignature.fill (parts (1 : Fin 2)) filling)) =
            LF.Term.app ((toContext (parts (0 : Fin 2))).fill fun index => toTerm (filling index))
              ((toContext (parts (1 : Fin 2))).fill fun index => toTerm (filling index))
          rw [ih (0 : Fin 2), ih (1 : Fin 2)]

theorem toContext_ofContext {arity : Type} (context : TermContext arity) :
    toContext (ofContext context) = context := by
  induction context with
  | hole slot => rfl
  | var index => rfl
  | srt sort => rfl
  | con name => rfl
  | pi domain body ihDomain ihBody =>
      show TermContext.pi (toContext (ofContext domain)) (toContext (ofContext body)) = _
      rw [ihDomain, ihBody]
  | lam domain body ihDomain ihBody =>
      show TermContext.lam (toContext (ofContext domain)) (toContext (ofContext body)) = _
      rw [ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      show TermContext.app (toContext (ofContext function)) (toContext (ofContext argument)) = _
      rw [ihFunction, ihArgument]

/-- Writing commutes with filling. -/
theorem ofTerm_fill {arity : Type} (context : TermContext arity) (filling : arity → LF.Term) :
    ofTerm (context.fill filling) =
      termSignature.fill (ofContext context) fun index => ofTerm (filling index) := by
  induction context with
  | hole slot => rfl
  | var index =>
      show termSignature.node (.var index) (fun position => position.elim0) =
        termSignature.node (.var index) _
      exact congrArg _ (funext fun position => position.elim0)
  | srt sort =>
      show termSignature.node (.srt sort) (fun position => position.elim0) =
        termSignature.node (.srt sort) _
      exact congrArg _ (funext fun position => position.elim0)
  | con name =>
      show termSignature.node (.con name) (fun position => position.elim0) =
        termSignature.node (.con name) _
      exact congrArg _ (funext fun position => position.elim0)
  | pi domain body ihDomain ihBody =>
      exact congrArg (termSignature.node (j := ()) TermFormer.pi)
        ((congrArg₂ two ihDomain ihBody).trans
          (comp_two (fun context => termSignature.fill context fun index => ofTerm (filling index))
            (ofContext domain) (ofContext body)).symm)
  | lam domain body ihDomain ihBody =>
      exact congrArg (termSignature.node (j := ()) TermFormer.lam)
        ((congrArg₂ two ihDomain ihBody).trans
          (comp_two (fun context => termSignature.fill context fun index => ofTerm (filling index))
            (ofContext domain) (ofContext body)).symm)
  | app function argument ihFunction ihArgument =>
      exact congrArg (termSignature.node (j := ()) TermFormer.app)
        ((congrArg₂ two ihFunction ihArgument).trans
          (comp_two (fun context => termSignature.fill context fun index => ofTerm (filling index))
            (ofContext function) (ofContext argument)).symm)

/-- A step between terms is a step between the terms of their derivations. -/
theorem step_ofTerm_iff {T : Theory} {first next : LF.Term} :
    Step T (toTerm (ofTerm first)) (toTerm (ofTerm next)) ↔ Step T first next := by
  rw [toTerm_ofTerm, toTerm_ofTerm]

theorem step_ofTerm_left {T : Theory} {first next : LF.Term} :
    Step T (toTerm (ofTerm first)) next ↔ Step T first next := by
  rw [toTerm_ofTerm]

theorem step_ofTerm_right {T : Theory} {first next : LF.Term} :
    Step T first (toTerm (ofTerm next)) ↔ Step T first next := by
  rw [toTerm_ofTerm]

/-! ## The calculus, in the common class -/

/-- The steps of a theory, as a reduction on the derivations of the formation
rules. -/
noncomputable def termReduction (T : Theory) :
    (termSignature.proofTheory (RuleSignature.ProofCongruence.identity _)).Reduction :=
  termSignature.reductionOfIdentity fun first second => Step T (toTerm first) (toTerm second)

/-- **The calculus of a theory, as a member of the common class.** -/
noncomputable def termTheory (T : Theory) : ContextTheory.{0} :=
  termSignature.reducingTheory (RuleSignature.ProofCongruence.identity _) (termReduction T)

theorem termTheory_reducing (T : Theory) : Reducing (termTheory T) :=
  ⟨_, termSignature, _, _, rfl⟩

/-- **From the member to the running presentation.** -/
noncomputable def formedMap (T : Theory) : ContextMap (termTheory T) (rewritingTheory T) where
  interface := fun _ => ()
  term := fun formed => toTerm formed
  context := fun context => toContext context
  term_resp := fun same => congrArg toTerm same
  equivariant := fun context filling => toTerm_fill context filling

/-- **The member is the running presentation**: nothing is lost. -/
theorem formedMap_hosting (T : Theory) : (formedMap T).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  refine ⟨fun same => toTerm_injective same, fun step => step, fun {_ first next} step => ?_⟩
  exact ⟨ofTerm next, step_ofTerm_right.mpr step, (toTerm_ofTerm next).symm⟩

/-- **And nothing is added.** -/
theorem formedMap_exhausting (T : Theory) : (formedMap T).Exhausting := by
  intro arity holes result observer
  exact ⟨ofContext observer, fun filling =>
    congrArg (TermContext.fill fun index => toTerm (filling index)) (toContext_ofContext observer)⟩

/-- From the running presentation to the member. -/
noncomputable def unformedMap (T : Theory) : ContextMap (rewritingTheory T) (termTheory T) where
  interface := fun _ => ()
  term := fun term => ofTerm term
  context := fun context => ofContext context
  term_resp := fun same => congrArg ofTerm same
  equivariant := fun context filling => ofTerm_fill context filling

theorem unformedMap_hosting (T : Theory) : (unformedMap T).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  refine ⟨fun same => ofTerm_injective same, fun {_ first next} step => ?_,
    fun {_ first next} step => ?_⟩
  · exact step_ofTerm_iff.mpr step
  · exact ⟨toTerm next, step_ofTerm_left.mp step, (ofTerm_toTerm next).symm⟩

/-- **The running presentation of every theory is, up to hosting both ways, a
member of the common class.** -/
theorem rewritingTheory_reducing (T : Theory) :
    ∃ member, Reducing member ∧ HostsExhaustively (rewritingTheory T) member ∧
      ∃ back : ContextMap (rewritingTheory T) member, back.Hosting :=
  ⟨termTheory T, termTheory_reducing T,
    ⟨formedMap T, formedMap_hosting T, formedMap_exhausting T⟩,
    unformedMap T, unformedMap_hosting T⟩

/-! ## Separation on the computational member -/

/-- **The syntax alone does not host the calculus**: forgetting the steps is
not hosting as soon as there is one. -/
theorem forgetSteps_not_hosting {T : Theory} {source target : LF.Term}
    (step : Step T source target) :
    ¬ ((ContextMap.id (termSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (termReduction T) (ContextTheory.Reduction.none _)).Hosting := by
  exact ContextMap.forget_not_hosting _ (termReduction T) (interface := ()) (term := ofTerm source)
    (next := ofTerm target) (step_ofTerm_iff.mpr step)

/-- In particular for beta alone. -/
theorem forgetBeta_not_hosting :
    ¬ ((ContextMap.id (termSignature.proofTheory (RuleSignature.ProofCongruence.identity _))).atReductions
        (termReduction Theory.empty) (ContextTheory.Reduction.none _)).Hosting :=
  forgetSteps_not_hosting
    (Mettapedia.GSLT.Dedukti.Step.root (.beta (.srt .type) (.var 0) (.srt .kind)))

/-! ## Both kinds in one host -/

/-- Three members: a proof system, the same with a normalization step, and a
calculus. -/
inductive Kind : Type where
  | logic
  | normalizing
  | calculus

/-- The judgments of each. -/
def Kind.Judgment : Kind → Type
  | .logic => IntFormula
  | .normalizing => IntFormula
  | .calculus => Unit

/-- The rules of each. -/
def Kind.signature : (kind : Kind) → RuleSignature kind.Judgment
  | .logic => intSignature
  | .normalizing => intSignature
  | .calculus => termSignature

/-- The reduction of each: none, the contraction of `K`, and the steps of the
theory. -/
noncomputable def Kind.step (T : Theory) :
    (kind : Kind) → {judgment : kind.Judgment} → kind.signature.Proof judgment →
      kind.signature.Proof judgment → Prop
  | .logic => fun _ _ => False
  | .normalizing => fun first second => Discards first second
  | .calculus => fun first second => Step T (toTerm first) (toTerm second)

/-- **One theory for the three.** -/
noncomputable def threeKinds (T : Theory) : ContextTheory.{0} :=
  sumReducing Kind.signature (Kind.step T)

/-- **The union hosts each of the three members.** -/
theorem threeKinds_hostsEvery (T : Theory) :
    HostsEvery (threeKinds T) (ReducingMember Kind.signature (Kind.step T)) :=
  sumReducing_hostsEvery Kind.signature (Kind.step T)

/-- The three members are the worked logic, the worked logic with its
reduction, and the calculus. -/
theorem kinds_members (T : Theory) :
    reducingMember Kind.signature (Kind.step T) .logic =
        intSignature.proofTheory (RuleSignature.ProofCongruence.identity _) ∧
      reducingMember Kind.signature (Kind.step T) .normalizing = intReducing ∧
      reducingMember Kind.signature (Kind.step T) .calculus = termTheory T :=
  ⟨rfl, rfl, rfl⟩

/-- **One host for a proof system, a proof system with reduction, and the
running presentation of a calculus.** -/
theorem threeKinds_hosts_rewritingTheory (T : Theory) :
    Reducing (threeKinds T) ∧
      (∃ map : ContextMap (intSignature.proofTheory (RuleSignature.ProofCongruence.identity _))
        (threeKinds T), map.Hosting) ∧
      (∃ map : ContextMap intReducing (threeKinds T), map.Hosting) ∧
      ∃ map : ContextMap (rewritingTheory T) (threeKinds T), map.Hosting :=
  ⟨sumReducing_reducing _ _,
    ⟨injectReducingMap Kind.signature (Kind.step T) .logic,
      injectReducingMap_hosting Kind.signature (Kind.step T) .logic⟩,
    ⟨injectReducingMap Kind.signature (Kind.step T) .normalizing,
      injectReducingMap_hosting Kind.signature (Kind.step T) .normalizing⟩,
    ⟨(injectReducingMap Kind.signature (Kind.step T) .calculus).comp (unformedMap T),
      (injectReducingMap_hosting Kind.signature (Kind.step T) .calculus).comp
        (unformedMap_hosting T)⟩⟩

#print axioms toTerm_ofTerm
#print axioms ofTerm_toTerm
#print axioms formedMap_hosting
#print axioms formedMap_exhausting
#print axioms unformedMap_hosting
#print axioms rewritingTheory_reducing
#print axioms forgetBeta_not_hosting
#print axioms threeKinds_hostsEvery
#print axioms threeKinds_hosts_rewritingTheory

end Mettapedia.Logic.HostingStyles
