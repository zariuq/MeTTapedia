import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetTheory
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation

/-!
# The laws of the sets in the tower inside the sets

The tower inside the sets with the constants of set theory (`MegalodonHOTG.SetTheory`) has a set model
in which the type of all sets is read as all the sets of one universe of Lean. This file shows
that the laws of the sets are true in that model, declares them as proof constants, and shows
that the package with them has a set model and is consistent.

**The laws** are eleven closed statements of a higher-order logic over the constants of the
sets (`ZFSetHenkinInterpretation`, `ZFSetUniverseInterpretation`): extensionality, the empty
set, the union, the power set, separation, replacement, induction on membership, and four laws
of the universe operation: a set is a member of its universe, and its universe is transitive,
closed under union, power set and replacement, and the least such set. They are true in the
model of that logic whose individuals are all the sets of a universe of Lean.

**The translation.** A type of the logic is a term of the package (`tyTm`): the propositions,
the type of all sets, the function types. A term of the logic is a term of the package
(`trTerm`): variables as indices, the constants as the constants of the package, an
abstraction with the term of its type as domain, and implication, equality and the universal
quantifier as the constants `imp`, `eq` and `all`. Truth, falsity, negation, conjunction,
disjunction and the existential quantifier are written with `imp` and `all` alone (`cTrue`,
`cFalse`, `cNot`, `cAnd`, `cOr`, `cEx`). Renaming and substitution commute with negation,
conjunction, disjunction and the existential quantifier (`cNot_rename`, `cAnd_rename`,
`cOr_rename`, `cEx_rename`, `cNot_subst`, `cAnd_subst`, `cOr_subst`, `cEx_subst`). Equal
propositions give equal conjunctions and disjunctions (`cAnd_congr`, `cOr_congr`), and the
existential quantifier of an abstraction is the written existential statement of its body
(`cEx_lam_eq`). The term of the law of the empty set is
`all set (λ x. imp (In x Empty) falsity)` (`trTerm_emptyLaw`).

**In the model**, at every assignment that gives the constants of set theory their values:

* the value of `imp`, `all`, `eq` and `In` at truth values and sets is the truth value of the
  implication, the universal statement, the equality and the membership (`ev_cImp`, `ev_cAll`,
  `ev_cEq`, `ev_cIn`, in `MegalodonHOTG.SetTheory`), and the same holds for the six written
  connectives (`ev_cTrue`, `ev_cFalse`, `ev_cNot`, `ev_cAnd`, `ev_cOr`, `ev_cEx`);
* the value of the term of a type is the set of the type (`ev_tyTm`): the truth values of the
  package, the subsets of `{∅}`, are the two truth values of the logic (`truthValues_eq`), and
  the set of every type is a member of the universe that reads `allClasses`
  (`typeCode_mem_classes`);
* **agreement** (`ev_trTerm`): the value of the term of a term of the logic, at the environment
  of a valuation, is the set under the value the logic gives the term;
* so the value of the type of the proofs of a closed statement is the truth value of the
  statement in the model of the logic (`ev_holds_trTerm`), and each of the eleven laws has a
  proof, the empty set (`extensionality_holds`, `emptyLaw_holds`, `unionLaw_holds`,
  `powerLaw_holds`, `separationLaw_holds`, `replacementLaw_holds`, `setInduction_holds`,
  `universeIn_holds`, `universeTransitive_holds`, `universeClosed_holds`,
  `universeMinimal_holds`).

**In the judgment**, in every package over the set theory, the term of a term of the logic has
the term of its type (`trTerm_typed`), so the proofs of a closed statement form a type of the
least universe (`holds_trTerm_typed`).

**The package with the laws** (`setLaws`): the tower inside the sets with the constants of set
theory and eleven proof constants, one for each law, with no equation. Every proof constant
has the type of the proofs of its law (`setLaws_typed`). The package has a set model with
every proof read as the empty set (`setLaws_setModel`), and no closed term of it proves that
the empty set is a member of itself (`setLaws_consistent`). The same holds for proof constants
of any list of closed statements that are true in the model of the logic (`withProofs`,
`withProofs_setModel`, `withProofs_consistent`). The package contains the steps of the
equations of the set theory (`withProofs_computes`).

**Hypotheses.** The model reads the tower by cofinally many inaccessible cardinals in the
upper universe, and the universe operation of the logic uses them in the lower universe. The
values of the connectives and the typings use neither. The seven laws of the sets are true at
the reading by the upper universe alone, whatever `UnivOf` is read as (`ev_trTerm_embed`,
`ev_holds_embed`). The four laws of the universe operation, and the set model of the package,
use both.

Positive examples: the proof constant of the law of the empty set is typed in the package
(`emptyLaw_typed`); every set is a member of its power set, in the model (`powerIn_holds`).
Negative examples: the statement that there is a set of all sets is false in the model
(`universalSet_false_in_model`), so the package that declares a proof of it has no set model
at this reading (`universalSet_no_setModel`).

The lemmas that join the trace interpretation of the logic to the package are stated here: the
constants of the logic are the constants of the package (`member_val`, `empty_val`,
`union_val`, `power_val`, `separate_val`, `replace_val`, `universe_val`), the two have the same
truth values (`truthValues_eq`), and the set of a type of the logic is a member of the
universe that reads `allClasses` (`typeCode_mem_classes`, `truthValues_mem_classes`). The set
under an abstraction of the logic (`lam_val`) is stated beside `app_val` in
`ZFSetHOLTraceTypeInterpretation`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles univOf)
open ZFSetDependentProducts (graph extendFunction extendFunction_at)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetHenkinInterpretation (replacement mem_replacement Symbol)
open ZFSetUniverseInterpretation (UniverseSymbol universeModel embed)
open ZFSetUniverseLift (carrierCode mem_carrierCode carrierCode_transitive lift lowerValue
  lift_lowerValue encode extendCarrierMap extendCarrierMap_at)
open ZFSetHOLTraceTypeInterpretation (typeCode Value lam app lam_val typeCode_mem prop_val
  truth_val holds_iff_empty_mem)
open ZFSetHOLTraceTermInterpretation (Valuation interpret constants universeConstants
  emptyValuation holds_interpret_core_iff holds_interpret_iff)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)

universe u

variable {L : Type}

/-! ## The truth values of the logic and of the package -/

section TruthValues

/-- **The truth values of the package are the truth values of the logic**: the subsets of
`{∅}` are `∅` and `{∅}`. -/
theorem truthValues_eq : truthValues.{u} = ZFSetHOLTypeInterpretation.truthCode.{u} := by
  apply ZFSet.ext
  intro z
  show z ∈ ZFSet.powerset {∅} ↔ z ∈ ({ZFSetHOLTypeInterpretation.falseSet,
    ZFSetHOLTypeInterpretation.trueSet} : ZFSet.{u})
  rw [ZFSet.mem_powerset, ZFSet.mem_pair]
  constructor
  · intro sub
    by_cases inhabited : (∅ : ZFSet.{u}) ∈ z
    · refine Or.inr (ZFSet.ext fun w => ⟨fun hw => sub hw, fun hw => ?_⟩)
      rw [ZFSet.mem_singleton.mp hw]
      exact inhabited
    · refine Or.inl (ZFSet.ext fun w =>
        ⟨fun hw => ?_, fun hw => absurd hw (ZFSet.notMem_empty w)⟩)
      exact absurd (ZFSet.mem_singleton.mp (sub hw) ▸ hw) inhabited
  · rintro (rfl | rfl)
    · exact ZFSet.empty_subset _
    · exact fun _ hw => hw

end TruthValues

/-! ## The constants of the logic are the constants of the package -/

section Constants

open ZFSetHenkinInterpretation (set predicate mapping)

/-- Membership. -/
theorem member_val : (constants.{u} Symbol.member).1 = inValue carrierCode.{u} := by
  unfold inValue
  exact lam_val (A := set) (B := .arr set .prop) _ _ fun x _ =>
    (lam_val (A := set) (B := .prop) _ _ fun y _ => (truth_val (x ∈ y)).symm).symm

/-- The empty set. -/
theorem empty_val : (constants.{u} Symbol.empty).1 = ∅ := rfl

/-- The union. -/
theorem union_val : (constants.{u} Symbol.union).1 = opValue carrierCode.{u} ZFSet.sUnion :=
  lam_val (A := set) (B := set) _ _ fun _ _ => rfl

/-- The power set. -/
theorem power_val : (constants.{u} Symbol.power).1 = opValue carrierCode.{u} ZFSet.powerset :=
  lam_val (A := set) (B := set) _ _ fun _ _ => rfl

/-- Separation: the predicate is a trace function into the truth values, true at a set when
the empty set is a member of its value there. -/
theorem separate_val : (constants.{u} Symbol.separate).1 = sepValue carrierCode.{u} := by
  unfold sepValue
  rw [truthValues_eq]
  refine lam_val (A := set) (B := .arr predicate set) _ _ fun a ha =>
    (lam_val (A := predicate) (B := set) _ _ fun p hp => ?_).symm
  show ZFSet.sep (fun x => (∅ : ZFSet.{u + 1}) ∈ traceApp p x) a =
    ZFSet.sep (fun x => ZFSetHOLTypeInterpretation.holds
      (app (A := set) (B := .prop) ⟨p, hp⟩ (encode (lowerValue x)))) a
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep, ZFSet.mem_sep]
  refine and_congr_right fun hx => ?_
  rw [holds_iff_empty_mem]
  show (∅ : ZFSet.{u + 1}) ∈ traceApp p x ↔
    (∅ : ZFSet.{u + 1}) ∈ traceApp p (lift (lowerValue x))
  rw [lift_lowerValue (carrierCode_transitive a ha hx)]

/-- Replacement: the function is a trace function on the sets. -/
theorem replace_val : (constants.{u} Symbol.replace).1 = replValue carrierCode.{u} := by
  unfold replValue
  refine lam_val (A := set) (B := .arr mapping set) _ _ fun a ha =>
    (lam_val (A := mapping) (B := set) _ _ fun f hf => ?_).symm
  show replacement a (fun x => traceApp f x) =
    replacement a (extendCarrierMap (app (A := set) (B := set) ⟨f, hf⟩))
  apply ZFSet.ext
  intro y
  rw [mem_replacement, mem_replacement]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, extendCarrierMap_at (app (A := set) (B := set) ⟨f, hf⟩)
      ⟨x, carrierCode_transitive a ha hx⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (extendCarrierMap_at (app (A := set) (B := set) ⟨f, hf⟩)
      ⟨x, carrierCode_transitive a ha hx⟩).symm⟩

/-- **The universe operation**: on the sets of the lower universe, the least closed universe
around a set taken in the upper universe is the one taken in the lower universe. -/
theorem universe_val (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1}) :
    (universeConstants small UniverseSymbol.universe).1 =
      opValue carrierCode.{u} (univOf large) := by
  refine lam_val (A := set) (B := set) _ _ fun x hx => ?_
  obtain ⟨y, rfl⟩ := mem_carrierCode.mp hx
  exact ZFSetLiftedUniverseClosure.larger_univOf_eq large y

end Constants

variable [LevelOrder L]

/-! ## The connectives of the package -/

section Connectives

variable {n : Nat}

/-- Falsity: `all prop (λ p. p)`. -/
def cFalse : CTm (Head L) n := cAll cProp (.lam cProp (.var 0))

/-- Negation: `imp p falsity`. -/
def cNot (p : CTm (Head L) n) : CTm (Head L) n := cImp p cFalse

/-- Truth: `all prop (λ p. imp p p)`. -/
def cTrue : CTm (Head L) n := cAll cProp (.lam cProp (cImp (.var 0) (.var 0)))

/-- Conjunction: `all prop (λ r. imp (imp p (imp q r)) r)`. -/
def cAnd (p q : CTm (Head L) n) : CTm (Head L) n :=
  cAll cProp (.lam cProp (cImp (cImp (p.rename wk) (cImp (q.rename wk) (.var 0))) (.var 0)))

/-- Disjunction: `all prop (λ r. imp (imp p r) (imp (imp q r) r))`. -/
def cOr (p q : CTm (Head L) n) : CTm (Head L) n :=
  cAll cProp (.lam cProp
    (cImp (cImp (p.rename wk) (.var 0)) (cImp (cImp (q.rename wk) (.var 0)) (.var 0))))

/-- The existential quantifier over a type, of a predicate on it:
`all prop (λ r. imp (all T (λ x. imp (P x) r)) r)`. -/
def cEx (T P : CTm (Head L) n) : CTm (Head L) n :=
  cAll cProp (.lam cProp
    (cImp (cAll (T.rename wk) (.lam (T.rename wk)
      (cImp (.app ((P.rename wk).rename wk) (.var 0)) (.var 1)))) (.var 0)))

section RenameSubst

variable {m : Nat}

omit [LevelOrder L] in
/-- Negation commutes with renaming. -/
theorem cNot_rename (r : Ren n m) (p : CTm (Head L) n) :
    (cNot p).rename r = cNot (p.rename r) := rfl

omit [LevelOrder L] in
/-- Conjunction commutes with renaming. -/
theorem cAnd_rename (r : Ren n m) (p q : CTm (Head L) n) :
    (cAnd p q).rename r = cAnd (p.rename r) (q.rename r) := by
  show cAll cProp (.lam cProp (cImp (cImp ((p.rename wk).rename (liftRen r))
    (cImp ((q.rename wk).rename (liftRen r)) (.var 0))) (.var 0))) = _
  rw [CTm.rename_liftRen_wk, CTm.rename_liftRen_wk]
  rfl

omit [LevelOrder L] in
/-- Disjunction commutes with renaming. -/
theorem cOr_rename (r : Ren n m) (p q : CTm (Head L) n) :
    (cOr p q).rename r = cOr (p.rename r) (q.rename r) := by
  show cAll cProp (.lam cProp (cImp (cImp ((p.rename wk).rename (liftRen r)) (.var 0))
    (cImp (cImp ((q.rename wk).rename (liftRen r)) (.var 0)) (.var 0)))) = _
  rw [CTm.rename_liftRen_wk, CTm.rename_liftRen_wk]
  rfl

omit [LevelOrder L] in
/-- The existential quantifier commutes with renaming. -/
theorem cEx_rename (r : Ren n m) (T P : CTm (Head L) n) :
    (cEx T P).rename r = cEx (T.rename r) (P.rename r) := by
  show cAll cProp (.lam cProp (cImp (cAll ((T.rename wk).rename (liftRen r))
    (.lam ((T.rename wk).rename (liftRen r))
      (cImp (.app (((P.rename wk).rename wk).rename (liftRen (liftRen r))) (.var 0)) (.var 1))))
    (.var 0))) = _
  rw [CTm.rename_liftRen_wk, CTm.rename_liftRen_wk, CTm.rename_liftRen_wk]
  rfl

omit [LevelOrder L] in
/-- Negation commutes with substitution. -/
theorem cNot_subst (s : CSub (Head L) n m) (p : CTm (Head L) n) :
    (cNot p).subst s = cNot (p.subst s) := rfl

omit [LevelOrder L] in
/-- Conjunction commutes with substitution. -/
theorem cAnd_subst (s : CSub (Head L) n m) (p q : CTm (Head L) n) :
    (cAnd p q).subst s = cAnd (p.subst s) (q.subst s) := by
  show cAll cProp (.lam cProp (cImp (cImp ((p.rename wk).subst (CTm.liftSub s))
    (cImp ((q.rename wk).subst (CTm.liftSub s)) (.var 0))) (.var 0))) = _
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]
  rfl

omit [LevelOrder L] in
/-- Disjunction commutes with substitution. -/
theorem cOr_subst (s : CSub (Head L) n m) (p q : CTm (Head L) n) :
    (cOr p q).subst s = cOr (p.subst s) (q.subst s) := by
  show cAll cProp (.lam cProp (cImp (cImp ((p.rename wk).subst (CTm.liftSub s)) (.var 0))
    (cImp (cImp ((q.rename wk).subst (CTm.liftSub s)) (.var 0)) (.var 0)))) = _
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]
  rfl

omit [LevelOrder L] in
/-- The existential quantifier commutes with substitution. -/
theorem cEx_subst (s : CSub (Head L) n m) (T P : CTm (Head L) n) :
    (cEx T P).subst s = cEx (T.subst s) (P.subst s) := by
  show cAll cProp (.lam cProp (cImp (cAll ((T.rename wk).subst (CTm.liftSub s))
    (.lam ((T.rename wk).subst (CTm.liftSub s))
      (cImp (.app (((P.rename wk).rename wk).subst (CTm.liftSub (CTm.liftSub s))) (.var 0))
        (.var 1))))
    (.var 0))) = _
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]
  rfl

end RenameSubst

section WrittenCongruence

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {Γ : CCtx (Head L) n}
  (covers : OverSetTheory Q)

include covers

/-- Conjunctions of equal propositions are equal. -/
theorem cAnd_congr {p p' q q' : CTm (Head L) n} (hp : CEqual Q Γ p p' cProp)
    (hq : CEqual Q Γ q q' cProp) : CEqual Q Γ (cAnd p q) (cAnd p' q') cProp :=
  cAll_lam_congr covers (prop_isClass covers)
    (cImp_congr covers
      (cImp_congr covers (hp.weaken (E := cProp))
        (cImp_congr covers (hq.weaken (E := cProp)) (.refl (.var 0))))
      (.refl (.var 0)))

/-- Disjunctions of equal propositions are equal. -/
theorem cOr_congr {p p' q q' : CTm (Head L) n} (hp : CEqual Q Γ p p' cProp)
    (hq : CEqual Q Γ q q' cProp) : CEqual Q Γ (cOr p q) (cOr p' q') cProp :=
  cAll_lam_congr covers (prop_isClass covers)
    (cImp_congr covers (cImp_congr covers (hp.weaken (E := cProp)) (.refl (.var 0)))
      (cImp_congr covers (cImp_congr covers (hq.weaken (E := cProp)) (.refl (.var 0)))
        (.refl (.var 0))))

/-- **The existential quantifier of an abstraction is the written existential statement of
its body**: the application of the predicate to the bound variable is its body. -/
theorem cEx_lam_eq {T : CTm (Head L) n} {body body' : CTm (Head L) (n + 1)}
    (hT : CTyped Q Γ T allClasses) (hbody : CTyped Q (.snoc Γ T) body cProp)
    (equal : CEqual Q (.snoc Γ T) body body' cProp) :
    CEqual Q Γ (cEx T (.lam T body))
      (cAll cProp (.lam cProp (cImp (cAll (T.rename wk) (.lam (T.rename wk)
        (cImp (body'.rename (liftRen wk)) (.var 1)))) (.var 0)))) cProp := by
  have domain : CTyped Q (.snoc Γ cProp) (T.rename wk) allClasses := hT.weaken (E := cProp)
  have lifted : CCtxRen (.snoc Γ T) (.snoc (.snoc Γ cProp) (T.rename wk)) (liftRen wk) :=
    (CCtxRen.wk Γ cProp).snoc T
  have inside : CTyped Q (.snoc (.snoc Γ cProp) (T.rename wk)) (body.rename (liftRen wk)) cProp :=
    hbody.rename lifted
  have beta : CEqual Q (.snoc (.snoc Γ cProp) (T.rename wk))
      (.app (((CTm.lam T body).rename wk).rename wk) (.var 0)) (body.rename (liftRen wk)) cProp :=
    predicate_apply_var covers domain inside
  have moved : CEqual Q (.snoc (.snoc Γ cProp) (T.rename wk)) (body.rename (liftRen wk))
      (body'.rename (liftRen wk)) cProp := equal.rename lifted
  exact cAll_lam_congr covers (prop_isClass covers)
    (cImp_congr covers
      (cAll_lam_congr covers domain (cImp_congr covers (.trans beta moved) (.refl (.var 1))))
      (.refl (.var 0)))

end WrittenCongruence

variable {heads : Head L → ZFSet.{u}} {consts : DeclName → ZFSet.{u}} {all classes : ZFSet.{u}}
  {around : ZFSet.{u} → ZFSet.{u}} (reads : Reads L all classes around consts)

include reads

variable (propClass : truthValues.{u} ∈ classes)

include propClass

/-- **Quantification over the propositions**: the value is the truth value of the
quantification over all statements. -/
theorem ev_cAll_prop {body : CTm (Head L) (n + 1)} {ρ : Env.{u} n} {Q : Prop → Prop}
    (value : ∀ R : Prop, ev heads consts body (extend ρ (truthCode R)) = truthCode (Q R)) :
    ev heads consts (cAll cProp (.lam cProp body)) ρ = truthCode (∀ R : Prop, Q R) := by
  have prop : ev heads consts (cProp : CTm (Head L) n) ρ = truthValues := reads.prop
  have step := ev_cAll_lam reads (T := cProp) (body := body) (ρ := ρ)
    (Q := fun x => Q ((∅ : ZFSet.{u}) ∈ x)) (by rw [prop]; exact propClass)
    (fun x hx => by
      rw [prop] at hx
      have known := value ((∅ : ZFSet.{u}) ∈ x)
      rwa [truthValue_eq hx] at known)
  rw [step, prop]
  congr 1
  apply propext
  constructor
  · intro h R
    have known := h (truthCode R) (truthCode_mem_truthValues R)
    rwa [propext (Square.square_truth_iff R)] at known
  · intro h x _
    exact h _

/-- **Falsity** is the false truth value. -/
theorem ev_cFalse (ρ : Env.{u} n) :
    ev heads consts (cFalse : CTm (Head L) n) ρ = truthCode False := by
  have step := ev_cAll_prop (heads := heads) reads propClass
    (body := (.var 0 : CTm (Head L) (n + 1))) (ρ := ρ) (Q := fun R => R) (fun _ => rfl)
  show ev heads consts (cAll cProp (.lam cProp (.var 0))) ρ = _
  rw [step]
  congr 1
  exact propext ⟨fun h => h False, False.elim⟩

/-- **Truth** is the true truth value. -/
theorem ev_cTrue (ρ : Env.{u} n) :
    ev heads consts (cTrue : CTm (Head L) n) ρ = truthCode True := by
  have step := ev_cAll_prop (heads := heads) reads propClass
    (body := (cImp (.var 0) (.var 0) : CTm (Head L) (n + 1))) (ρ := ρ) (Q := fun R => R → R)
    (fun _ => ev_cImp reads rfl rfl)
  show ev heads consts (cAll cProp (.lam cProp (cImp (.var 0) (.var 0)))) ρ = _
  rw [step]
  congr 1
  exact propext ⟨fun _ => trivial, fun _ _ h => h⟩

/-- **Negation**: at the truth value of a statement, the truth value of its negation. -/
theorem ev_cNot {p : CTm (Head L) n} {ρ : Env.{u} n} {P : Prop}
    (hp : ev heads consts p ρ = truthCode P) : ev heads consts (cNot p) ρ = truthCode (¬ P) :=
  ev_cImp reads hp (ev_cFalse reads propClass ρ)

/-- **Conjunction**: at the truth values of two statements, the truth value of their
conjunction. -/
theorem ev_cAnd {p q : CTm (Head L) n} {ρ : Env.{u} n} {P Q : Prop}
    (hp : ev heads consts p ρ = truthCode P) (hq : ev heads consts q ρ = truthCode Q) :
    ev heads consts (cAnd p q) ρ = truthCode (P ∧ Q) := by
  have step := ev_cAll_prop reads propClass (ρ := ρ)
    (body := cImp (cImp (p.rename wk) (cImp (q.rename wk) (.var 0))) (.var 0))
    (Q := fun R => (P → Q → R) → R)
    (fun _ => ev_cImp reads
      (ev_cImp reads ((ev_rename_wk heads consts p ρ _).trans hp)
        (ev_cImp reads ((ev_rename_wk heads consts q ρ _).trans hq) rfl)) rfl)
  show ev heads consts (cAll cProp (.lam cProp
    (cImp (cImp (p.rename wk) (cImp (q.rename wk) (.var 0))) (.var 0)))) ρ = _
  rw [step]
  congr 1
  exact propext ⟨fun h => h (P ∧ Q) And.intro, fun h _ f => f h.1 h.2⟩

/-- **Disjunction**: at the truth values of two statements, the truth value of their
disjunction. -/
theorem ev_cOr {p q : CTm (Head L) n} {ρ : Env.{u} n} {P Q : Prop}
    (hp : ev heads consts p ρ = truthCode P) (hq : ev heads consts q ρ = truthCode Q) :
    ev heads consts (cOr p q) ρ = truthCode (P ∨ Q) := by
  have step := ev_cAll_prop reads propClass (ρ := ρ)
    (body := cImp (cImp (p.rename wk) (.var 0)) (cImp (cImp (q.rename wk) (.var 0)) (.var 0)))
    (Q := fun R => (P → R) → (Q → R) → R)
    (fun _ => ev_cImp reads
      (ev_cImp reads ((ev_rename_wk heads consts p ρ _).trans hp) rfl)
      (ev_cImp reads (ev_cImp reads ((ev_rename_wk heads consts q ρ _).trans hq) rfl) rfl))
  show ev heads consts (cAll cProp (.lam cProp
    (cImp (cImp (p.rename wk) (.var 0)) (cImp (cImp (q.rename wk) (.var 0)) (.var 0))))) ρ = _
  rw [step]
  congr 1
  exact propext ⟨fun h => h (P ∨ Q) Or.inl Or.inr, fun h _ f g => h.elim f g⟩

/-- **The existential quantifier**: over a type of `allClasses`, of a predicate whose values
on the type are the truth values of statements, the truth value of the existential
statement. -/
theorem ev_cEx {T P : CTm (Head L) n} {ρ : Env.{u} n} {Q : ZFSet.{u} → Prop}
    (hT : ev heads consts T ρ ∈ classes)
    (value : ∀ x ∈ ev heads consts T ρ, traceApp (ev heads consts P ρ) x = truthCode (Q x)) :
    ev heads consts (cEx T P) ρ = truthCode (∃ x ∈ ev heads consts T ρ, Q x) := by
  have step := ev_cAll_prop reads propClass (ρ := ρ)
    (body := cImp (cAll (T.rename wk) (.lam (T.rename wk)
      (cImp (.app ((P.rename wk).rename wk) (.var 0)) (.var 1)))) (.var 0))
    (Q := fun R => (∀ x ∈ ev heads consts T ρ, Q x → R) → R)
    (fun R => by
      have domain : ev heads consts (T.rename wk) (extend ρ (truthCode R)) =
          ev heads consts T ρ := ev_rename_wk heads consts T ρ _
      have inner := ev_cAll_lam reads (T := T.rename wk)
        (body := cImp (.app ((P.rename wk).rename wk) (.var 0)) (.var 1))
        (ρ := extend ρ (truthCode R)) (Q := fun x => Q x → R)
        (by rw [domain]; exact hT)
        (fun x hx => by
          rw [domain] at hx
          refine ev_cImp reads ?_ rfl
          show traceApp (ev heads consts ((P.rename wk).rename wk)
            (extend (extend ρ (truthCode R)) x)) x = _
          rw [ev_rename_wk, ev_rename_wk]
          exact value x hx)
      rw [domain] at inner
      exact ev_cImp reads inner rfl)
  show ev heads consts (cAll cProp (.lam cProp
    (cImp (cAll (T.rename wk) (.lam (T.rename wk)
      (cImp (.app ((P.rename wk).rename wk) (.var 0)) (.var 1)))) (.var 0)))) ρ = _
  rw [step]
  congr 1
  exact propext ⟨fun h => h (∃ x ∈ ev heads consts T ρ, Q x) fun x hx q => ⟨x, hx, q⟩,
    fun ⟨x, hx, q⟩ _ f => f x hx q⟩

end Connectives

/-! ## The translation -/

section Translation

/-- **The term of a type of the logic**: the propositions, the type of all sets, and the
function types. -/
def tyTm : Ty Unit → {n : Nat} → CTm (Head L) n
  | .prop, _ => cProp
  | .base _, _ => allSets
  | .arr A B, _ => .pi (tyTm A) (tyTm B)

/-- The index of a variable of the logic: the newest variable is `0`. -/
def varIndex : {Γ : Ctx Unit} → {A : Ty Unit} → Var Γ A → Fin Γ.length
  | _ :: Γ, _, .vz => (0 : Fin (Γ.length + 1))
  | _ :: _, _, .vs v => (varIndex v).succ

/-- **The term of a term of the logic over any constants**, given the constant of the package
for each of them: variables as indices, an abstraction with the term of its type as domain,
implication, equality and the universal quantifier as the constants `imp`, `eq` and `all`, and
the other connectives by their definitions from `imp` and `all`. -/
def trWith {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName) :
    {Γ : Ctx Unit} → {A : Ty Unit} → Term Const Γ A → CTm (Head L) Γ.length
  | _, _, .var v => .var (varIndex v)
  | _, _, .const c => .const (name c)
  | _, _, .app f x => .app (trWith name f) (trWith name x)
  | _, _, .lam (σ := σ) body => .lam (tyTm σ) (trWith name body)
  | _, _, .top => cTrue
  | _, _, .bot => cFalse
  | _, _, .and p q => cAnd (trWith name p) (trWith name q)
  | _, _, .or p q => cOr (trWith name p) (trWith name q)
  | _, _, .imp p q => cImp (trWith name p) (trWith name q)
  | _, _, .not p => cNot (trWith name p)
  | _, _, .eq (τ := τ) x y => cEq (tyTm τ) (trWith name x) (trWith name y)
  | _, _, .all (σ := σ) p => cAll (tyTm σ) (.lam (tyTm σ) (trWith name p))
  | _, _, .ex (σ := σ) p => cEx (tyTm σ) (.lam (tyTm σ) (trWith name p))

/-- The constant of the package for a constant of the sets. -/
def coreName : {A : Ty Unit} → Symbol A → DeclName
  | _, .member => inN
  | _, .empty => emptyN
  | _, .union => unionN
  | _, .power => powerN
  | _, .separate => sepN
  | _, .replace => replN

/-- The constant of the package for a constant of the sets with the universe operation. -/
def constName : {A : Ty Unit} → UniverseSymbol A → DeclName
  | _, .core c => coreName c
  | _, .universe => univOfN

/-- **The term of a term of the logic of the sets with the universe operation.** -/
def trTerm {Γ : Ctx Unit} {A : Ty Unit} (t : Term UniverseSymbol Γ A) : CTm (Head L) Γ.length :=
  trWith constName t

omit [LevelOrder L] in
/-- The term of a term without the universe operation is the term of the same term over the
constants of the sets alone. -/
theorem trTerm_embed {Γ : Ctx Unit} {A : Ty Unit} (t : Term Symbol Γ A) :
    (trTerm (embed t) : CTm (Head L) Γ.length) = trWith coreName t := by
  unfold trTerm embed
  induction t with
  | var v => rfl
  | const c =>
    show trWith constName (Mettapedia.Logic.HOL.weakenCtx _
      (.const (.core c) : Mettapedia.Logic.HOL.ClosedTerm UniverseSymbol _)) = _
    rw [Mettapedia.Logic.HOL.weakenCtx_const]
    rfl
  | app f x ihf ihx => exact congrArg₂ CTm.app ihf ihx
  | lam body ih => exact congrArg (CTm.lam (tyTm _)) ih
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => exact congrArg₂ cAnd ihp ihq
  | or p q ihp ihq => exact congrArg₂ cOr ihp ihq
  | imp p q ihp ihq => exact congrArg₂ (fun a b => cImp a b) ihp ihq
  | not p ih => exact congrArg cNot ih
  | eq x y ihx ihy => exact congrArg₂ (fun a b => cEq (tyTm _) a b) ihx ihy
  | all p ih => exact congrArg (fun a => cAll (tyTm _) (.lam (tyTm _) a)) ih
  | ex p ih => exact congrArg (fun a => cEx (tyTm _) (.lam (tyTm _) a)) ih

/-- **The environment of a valuation**: the sets under its values. -/
def envOf : {Γ : Ctx Unit} → Valuation.{u} Γ → Env.{u + 1} Γ.length
  | [], _ => Fin.elim0
  | _ :: _, ρ => extend (envOf fun {_} v => ρ (.vs v)) (ρ .vz).1

/-- The environment of a valuation gives a variable the set under its value. -/
theorem envOf_varIndex : ∀ {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ) (v : Var Γ A),
    envOf ρ (varIndex v) = (ρ v).1
  | _ :: _, _, _, .vz => rfl
  | _ :: _, _, ρ, .vs v => envOf_varIndex (fun {_} w => ρ (.vs w)) v

/-- Extending a valuation extends its environment. -/
theorem envOf_extend {Γ : Ctx Unit} {A : Ty Unit} (ρ : Valuation.{u} Γ) (x : Value.{u} A) :
    envOf (ZFSetHOLTraceTermInterpretation.extend ρ x) = extend (envOf ρ) x.1 := rfl

end Translation

/-! ## The translation in the judgment -/

section Typing

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}

omit [LevelOrder L] in
/-- The term of a type of the logic is closed: renaming leaves it as it is. -/
theorem tyTm_rename (A : Ty Unit) : ∀ {n m : Nat} (r : Ren n m),
    (tyTm A : CTm (Head L) n).rename r = tyTm A := by
  induction A with
  | prop => exact fun _ => rfl
  | base b => exact fun _ => rfl
  | arr A B ihA ihB =>
    intro n m r
    show CTm.pi ((tyTm A : CTm (Head L) n).rename r)
      ((tyTm B : CTm (Head L) (n + 1)).rename (liftRen r)) = CTm.pi (tyTm A) (tyTm B)
    rw [ihA r, ihB (liftRen r)]

omit [LevelOrder L] in
/-- The term of a type of the logic is closed: substitution leaves it as it is. -/
theorem tyTm_subst (A : Ty Unit) : ∀ {n m : Nat} (s : CSub (Head L) n m),
    (tyTm A : CTm (Head L) n).subst s = tyTm A := by
  induction A with
  | prop => exact fun _ => rfl
  | base b => exact fun _ => rfl
  | arr A B ihA ihB =>
    intro n m s
    show CTm.pi ((tyTm A : CTm (Head L) n).subst s)
      ((tyTm B : CTm (Head L) (n + 1)).subst (CTm.liftSub s)) = CTm.pi (tyTm A) (tyTm B)
    rw [ihA s, ihB (CTm.liftSub s)]

/-- **The context of a context of the logic**: the terms of its types. -/
def ctxTm : (Γ : Ctx Unit) → CCtx (Head L) Γ.length
  | [] => .nil
  | A :: Γ => .snoc (ctxTm Γ) (tyTm A)

omit [LevelOrder L] in
/-- The context gives a variable the term of its type. -/
theorem lookup_ctxTm : ∀ {Γ : Ctx Unit} {A : Ty Unit} (v : Var Γ A),
    (ctxTm Γ : CCtx (Head L) Γ.length).lookup (varIndex v) = tyTm A
  | _ :: _, _, .vz => tyTm_rename _ wk
  | _ :: Γ, _, .vs v => by
    show ((ctxTm Γ : CCtx (Head L) Γ.length).lookup (varIndex v)).rename wk = _
    rw [lookup_ctxTm v, tyTm_rename]

variable (covers : OverSetTheory Q)

include covers

/-- A quantification over the propositions is a proposition. -/
theorem cAll_prop_typed {body : CTm (Head L) (n + 1)}
    (hbody : CTyped Q (.snoc Γ cProp) body cProp) :
    CTyped Q Γ (cAll cProp (.lam cProp body)) cProp :=
  cAll_typed covers (prop_isClass covers)
    (.lamIntro (prop_isClass covers) (covers.contains.isUniverse (.sort _))
      (classToClass_typed covers.contains (prop_isClass covers) (prop_isClass covers))
      (covers.contains.isUniverse (.sort _)) hbody)

/-- Falsity is a proposition. -/
theorem cFalse_typed : CTyped Q Γ cFalse cProp :=
  cAll_prop_typed covers (.var 0)

/-- Truth is a proposition. -/
theorem cTrue_typed : CTyped Q Γ cTrue cProp :=
  cAll_prop_typed covers (cImp_typed covers (.var 0) (.var 0))

/-- The negation of a proposition is a proposition. -/
theorem cNot_typed {p : CTm (Head L) n} (hp : CTyped Q Γ p cProp) : CTyped Q Γ (cNot p) cProp :=
  cImp_typed covers hp (cFalse_typed covers)

/-- The conjunction of two propositions is a proposition. -/
theorem cAnd_typed {p q : CTm (Head L) n} (hp : CTyped Q Γ p cProp) (hq : CTyped Q Γ q cProp) :
    CTyped Q Γ (cAnd p q) cProp :=
  cAll_prop_typed covers
    (cImp_typed covers
      (cImp_typed covers (hp.weaken (E := cProp))
        (cImp_typed covers (hq.weaken (E := cProp)) (.var 0))) (.var 0))

/-- The disjunction of two propositions is a proposition. -/
theorem cOr_typed {p q : CTm (Head L) n} (hp : CTyped Q Γ p cProp) (hq : CTyped Q Γ q cProp) :
    CTyped Q Γ (cOr p q) cProp :=
  cAll_prop_typed covers
    (cImp_typed covers (cImp_typed covers (hp.weaken (E := cProp)) (.var 0))
      (cImp_typed covers (cImp_typed covers (hq.weaken (E := cProp)) (.var 0)) (.var 0)))

/-- **An existential quantification over a type of `allClasses` is a proposition.** -/
theorem cEx_typed {T P : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CTyped Q Γ P (.pi T cProp)) : CTyped Q Γ (cEx T P) cProp := by
  have domain : CTyped Q (.snoc Γ cProp) (T.rename wk) allClasses := hT.weaken (E := cProp)
  have predicate : CTyped Q (.snoc (.snoc Γ cProp) (T.rename wk)) ((P.rename wk).rename wk)
      (.pi ((T.rename wk).rename wk) cProp) :=
    (hP.weaken (E := cProp)).weaken (E := T.rename wk)
  have applied : CTyped Q (.snoc (.snoc Γ cProp) (T.rename wk))
      (.app ((P.rename wk).rename wk) (.var 0)) cProp :=
    .appElim (B := cProp) predicate (.var 0)
  exact cAll_prop_typed covers
    (cImp_typed covers
      (cAll_typed covers domain
        (.lamIntro domain (covers.contains.isUniverse (.sort _))
          (classToClass_typed covers.contains domain (prop_isClass covers))
          (covers.contains.isUniverse (.sort _))
          (cImp_typed covers applied (.var 1))))
      (.var 0))

/-- **The term of a type of the logic is a type of `allClasses`.** -/
theorem tyTm_typed (A : Ty Unit) : ∀ {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (tyTm A) allClasses := by
  induction A with
  | prop => exact prop_isClass covers
  | base b => exact sets_typed covers.contains
  | arr A B ihA ihB => exact classToClass_typed covers.contains ihA ihB

/-- A constant of the sets has the term of its type. -/
theorem coreName_typed : ∀ {A : Ty Unit} (c : Symbol A) {n : Nat} {Γ : CCtx (Head L) n},
    CTyped Q Γ (.const (coreName c)) (tyTm A)
  | _, .member, _, _ => in_typed covers
  | _, .empty, _, _ => empty_typed covers
  | _, .union, _, _ => union_typed covers
  | _, .power, _, _ => power_typed covers
  | _, .separate, _, _ => sep_typed covers
  | _, .replace, _, _ => repl_typed covers

/-- A constant of the sets with the universe operation has the term of its type. -/
theorem constName_typed : ∀ {A : Ty Unit} (c : UniverseSymbol A) {n : Nat}
    {Γ : CCtx (Head L) n}, CTyped Q Γ (.const (constName c)) (tyTm A)
  | _, .core c, _, _ => coreName_typed covers c
  | _, .universe, _, _ => univOf_typed covers

/-- **The term of a term of the logic has the term of its type**, in the context of its
context, in every package over the set theory, when the constants have the terms of their
types. -/
theorem trWith_typed {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
    (named : ∀ {A : Ty Unit} (c : Const A) {n : Nat} {Γ : CCtx (Head L) n},
      CTyped Q Γ (.const (name c)) (tyTm A))
    {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    CTyped Q (ctxTm Γ) (trWith name t) (tyTm A) := by
  induction t with
  | var v => exact lookup_ctxTm v ▸ CDerivable.var (varIndex v)
  | const c => exact named c
  | @app Γ σ τ f x ihf ihx =>
    have step := CDerivable.appElim ihf ihx
    rwa [show CTm.inst0 (trWith name x) (tyTm τ) = tyTm τ from tyTm_subst τ _] at step
  | @lam σ Γ τ body ih =>
    exact .lamIntro (tyTm_typed covers σ) (covers.contains.isUniverse (.sort _))
      (tyTm_typed covers (.arr σ τ)) (covers.contains.isUniverse (.sort _)) ih
  | top => exact cTrue_typed covers
  | bot => exact cFalse_typed covers
  | and p q ihp ihq => exact cAnd_typed covers ihp ihq
  | or p q ihp ihq => exact cOr_typed covers ihp ihq
  | imp p q ihp ihq => exact cImp_typed covers ihp ihq
  | not p ih => exact cNot_typed covers ih
  | @eq Γ τ x y ihx ihy => exact cEq_typed covers (tyTm_typed covers τ) ihx ihy
  | @all σ Γ p ih =>
    exact cAll_typed covers (tyTm_typed covers σ)
      (.lamIntro (tyTm_typed covers σ) (covers.contains.isUniverse (.sort _))
        (classToClass_typed covers.contains (tyTm_typed covers σ) (prop_isClass covers))
        (covers.contains.isUniverse (.sort _)) ih)
  | @ex σ Γ p ih =>
    exact cEx_typed covers (tyTm_typed covers σ)
      (.lamIntro (tyTm_typed covers σ) (covers.contains.isUniverse (.sort _))
        (classToClass_typed covers.contains (tyTm_typed covers σ) (prop_isClass covers))
        (covers.contains.isUniverse (.sort _)) ih)

/-- **The term of a term of the logic of the sets with the universe operation has the term of
its type.** -/
theorem trTerm_typed {Γ : Ctx Unit} {A : Ty Unit} (t : Term UniverseSymbol Γ A) :
    CTyped Q (ctxTm Γ) (trTerm t) (tyTm A) :=
  trWith_typed covers constName (constName_typed covers) t

/-- **The proofs of a closed statement form a type of the least universe.** -/
theorem holds_trTerm_typed (φ : ClosedFormula UniverseSymbol) :
    CTyped Q .nil (cHolds (trTerm φ)) U0 :=
  cHolds_typed covers (trTerm_typed covers φ)

end Typing

/-! ## The translation in the model -/

section Agreement

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} {ν : Nat → Above L} {consts : DeclName → ZFSet.{u + 1}}
  {around : ZFSet.{u + 1} → ZFSet.{u + 1}}

/-- **The set of a type of the logic is a member of the universe that reads `allClasses`.** -/
theorem typeCode_mem_classes (A : Ty Unit) :
    typeCode.{u} A ∈ stages (L := L) large (.above 1) :=
  typeCode_mem (universeSet_closed large carrierCode 0)
    (seed_mem_universeSet large carrierCode 0) A

/-- The truth values are a member of the universe that reads `allClasses`. -/
theorem truthValues_mem_classes : truthValues.{u + 1} ∈ stages (L := L) large (.above 1) := by
  rw [truthValues_eq]
  exact typeCode_mem_classes large .prop

section Reading

variable (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
  around consts)

include reads

/-- **The value of the term of a type of the logic is the set of the type.** -/
theorem ev_tyTm (A : Ty Unit) : ∀ {n : Nat} (ρ : Env.{u + 1} n),
    ev (lowerSetsHeads (L := L) large ground ν) consts (tyTm A) ρ = typeCode.{u} A := by
  induction A with
  | prop =>
    intro n ρ
    show consts propN = ZFSetHOLTypeInterpretation.truthCode
    rw [reads.prop, truthValues_eq]
  | base b =>
    intro n ρ
    rfl
  | arr A B ihA ihB =>
    intro n ρ
    show tracePiSet (ev (lowerSetsHeads (L := L) large ground ν) consts (tyTm A) ρ)
      (fun x => ev (lowerSetsHeads (L := L) large ground ν) consts (tyTm B) (extend ρ x)) =
        tracePiSet (typeCode.{u} A) fun _ => typeCode.{u} B
    rw [ihA ρ]
    exact tracePiSet_congr fun x _ => ihB (extend ρ x)

/-- **The value of a constant of the sets is the set under the constant of the logic.** -/
theorem coreName_val : ∀ {A : Ty Unit} (c : Symbol A), consts (coreName c) = (constants.{u} c).1
  | _, .member => reads.in.trans member_val.symm
  | _, .empty => reads.empty
  | _, .union => reads.union.trans union_val.symm
  | _, .power => reads.power.trans power_val.symm
  | _, .separate => reads.sep.trans separate_val.symm
  | _, .replace => reads.repl.trans replace_val.symm

/-- **Agreement**, for a logic over any constants whose values in the package are the sets
under their values in the logic: the value of the term of a term of the logic, at the
environment of a valuation, is the set under the value the logic gives the term at the
valuation. -/
theorem ev_trWith {Const : Ty Unit → Type} (name : {A : Ty Unit} → Const A → DeclName)
    (values : {A : Ty Unit} → Const A → Value.{u} A)
    (named : ∀ {A : Ty Unit} (c : Const A), consts (name c) = (values c).1)
    {Γ : Ctx Unit} {A : Ty Unit} (t : Term Const Γ A) :
    ∀ ρ : Valuation.{u} Γ,
      ev (lowerSetsHeads (L := L) large ground ν) consts (trWith name t) (envOf ρ) =
        (interpret values t ρ).1 := by
  have propClass := truthValues_mem_classes (L := L) large
  induction t with
  | var v =>
    intro ρ
    exact envOf_varIndex ρ v
  | const c =>
    intro ρ
    exact named c
  | app f x ihf ihx =>
    intro ρ
    show traceApp (ev (lowerSetsHeads (L := L) large ground ν) consts (trWith name f) (envOf ρ))
      (ev (lowerSetsHeads (L := L) large ground ν) consts (trWith name x) (envOf ρ)) =
        traceApp (interpret values f ρ).1 (interpret values x ρ).1
    rw [ihf ρ, ihx ρ]
  | @lam σ Γ τ body ih =>
    intro ρ
    show traceLam (graph (ev (lowerSetsHeads (L := L) large ground ν) consts (tyTm σ) (envOf ρ))
      (fun x => ev (lowerSetsHeads (L := L) large ground ν) consts (trWith name body)
        (extend (envOf ρ) x))) =
      (lam fun x => interpret values body (ZFSetHOLTraceTermInterpretation.extend ρ x)).1
    rw [ev_tyTm large reads σ (envOf ρ)]
    exact (lam_val _ _ fun x hx => ih (ZFSetHOLTraceTermInterpretation.extend ρ ⟨x, hx⟩)).symm
  | top =>
    intro ρ
    exact (ev_cTrue reads propClass _).trans (truth_val True).symm
  | bot =>
    intro ρ
    exact (ev_cFalse reads propClass _).trans (truth_val False).symm
  | and p q ihp ihq =>
    intro ρ
    exact (ev_cAnd reads propClass ((ihp ρ).trans (prop_val _))
      ((ihq ρ).trans (prop_val _))).trans (truth_val _).symm
  | or p q ihp ihq =>
    intro ρ
    exact (ev_cOr reads propClass ((ihp ρ).trans (prop_val _))
      ((ihq ρ).trans (prop_val _))).trans (truth_val _).symm
  | imp p q ihp ihq =>
    intro ρ
    exact (ev_cImp reads ((ihp ρ).trans (prop_val _))
      ((ihq ρ).trans (prop_val _))).trans (truth_val _).symm
  | not p ih =>
    intro ρ
    exact (ev_cNot reads propClass ((ih ρ).trans (prop_val _))).trans (truth_val _).symm
  | @eq Γ τ x y ihx ihy =>
    intro ρ
    have type := ev_tyTm large reads (ground := ground) (ν := ν) τ (envOf ρ)
    have step := ev_cEq reads (heads := lowerSetsHeads (L := L) large ground ν) (T := tyTm τ)
      (a := trWith name x) (b := trWith name y) (ρ := envOf ρ)
      (by rw [type]; exact typeCode_mem_classes large τ)
      (by rw [type, ihx ρ]; exact (interpret values x ρ).2)
      (by rw [type, ihy ρ]; exact (interpret values y ρ).2)
    refine step.trans ?_
    rw [ihx ρ, ihy ρ]
    refine Eq.trans ?_ (truth_val _).symm
    congr 1
    exact propext Subtype.ext_iff.symm
  | @all σ Γ p ih =>
    intro ρ
    have type := ev_tyTm large reads (ground := ground) (ν := ν) σ (envOf ρ)
    have step := ev_cAll_lam reads (heads := lowerSetsHeads (L := L) large ground ν)
      (T := tyTm σ) (body := trWith name p) (ρ := envOf ρ)
      (Q := fun x => ∀ hx : x ∈ typeCode.{u} σ, ZFSetHOLTypeInterpretation.holds
        (interpret values p (ZFSetHOLTraceTermInterpretation.extend ρ ⟨x, hx⟩)))
      (by rw [type]; exact typeCode_mem_classes large σ)
      (fun x hx => by
        rw [type] at hx
        refine ((ih (ZFSetHOLTraceTermInterpretation.extend ρ ⟨x, hx⟩)).trans
          (prop_val _)).trans ?_
        congr 1
        exact propext ⟨fun h _ => h, fun h => h hx⟩)
    refine step.trans ?_
    rw [type]
    refine Eq.trans ?_ (truth_val _).symm
    congr 1
    exact propext ⟨fun h x => h x.1 x.2 x.2, fun h x _ hx => h ⟨x, hx⟩⟩
  | @ex σ Γ p ih =>
    intro ρ
    have type := ev_tyTm large reads (ground := ground) (ν := ν) σ (envOf ρ)
    have step := ev_cEx reads propClass (heads := lowerSetsHeads (L := L) large ground ν)
      (T := tyTm σ) (P := .lam (tyTm σ) (trWith name p)) (ρ := envOf ρ)
      (Q := fun x => ∃ hx : x ∈ typeCode.{u} σ, ZFSetHOLTypeInterpretation.holds
        (interpret values p (ZFSetHOLTraceTermInterpretation.extend ρ ⟨x, hx⟩)))
      (by rw [type]; exact typeCode_mem_classes large σ)
      (fun x hx => by
        show traceApp (traceLam (graph
          (ev (lowerSetsHeads (L := L) large ground ν) consts (tyTm σ) (envOf ρ))
          fun y => ev (lowerSetsHeads (L := L) large ground ν) consts (trWith name p)
            (extend (envOf ρ) y))) x = _
        rw [traceApp_graph_beta _ hx]
        rw [type] at hx
        refine ((ih (ZFSetHOLTraceTermInterpretation.extend ρ ⟨x, hx⟩)).trans
          (prop_val _)).trans ?_
        congr 1
        exact propext ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩)
    refine step.trans ?_
    rw [type]
    refine Eq.trans ?_ (truth_val _).symm
    congr 1
    exact propext ⟨fun ⟨x, _, hx, h⟩ => ⟨⟨x, hx⟩, h⟩, fun ⟨x, h⟩ => ⟨x.1, x.2, x.2, h⟩⟩

/-- **Agreement without the universe operation**: no hypothesis on the lower universe, and
whatever `UnivOf` is read as. -/
theorem ev_trTerm_embed {Γ : Ctx Unit} {A : Ty Unit} (t : Term Symbol Γ A)
    (ρ : Valuation.{u} Γ) :
    ev (lowerSetsHeads (L := L) large ground ν) consts (trTerm (embed t)) (envOf ρ) =
      (interpret constants t ρ).1 := by
  rw [trTerm_embed]
  exact ev_trWith large reads coreName constants (coreName_val large reads) t ρ

end Reading

variable (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
  (univOf large) consts)

include reads

/-- **The value of a constant of the package is the set under the constant of the logic.**
The universe operation of the logic is the least closed universe in the lower universe; the
package reads `UnivOf` as the least closed universe in the upper one. -/
theorem constName_val : ∀ {A : Ty Unit} (c : UniverseSymbol A),
    consts (constName c) = (universeConstants small c).1
  | _, .core c => coreName_val large reads c
  | _, .universe => reads.univOf.trans (universe_val small large).symm

/-- **Agreement**: the value of the term of a term of the logic, at the environment of a
valuation, is the set under the value the logic gives the term at the valuation. -/
theorem ev_trTerm {Γ : Ctx Unit} {A : Ty Unit} (t : Term UniverseSymbol Γ A)
    (ρ : Valuation.{u} Γ) :
    ev (lowerSetsHeads (L := L) large ground ν) consts (trTerm t) (envOf ρ) =
      (interpret (universeConstants small) t ρ).1 :=
  ev_trWith large reads constName (universeConstants small) (constName_val small large reads) t ρ

end Agreement

/-! ## Closed statements -/

section Truth

open ZFSetUniverseInterpretation (models_embed)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} {ν : Nat → Above L} {consts : DeclName → ZFSet.{u + 1}}
  {around : ZFSet.{u + 1} → ZFSet.{u + 1}}

/-- **The proofs of a closed statement of the sets**: the value of the type of the proofs of
its term is the truth value of the statement in the model whose individuals are all the sets.
No hypothesis on the lower universe, and whatever `UnivOf` is read as. -/
theorem ev_holds_embed
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) (φ : ClosedFormula Symbol) :
    ev (lowerSetsHeads (L := L) large ground ν) consts (cHolds (trTerm (embed φ))) Fin.elim0 =
      truthCode (ZFSetHenkinInterpretation.model.{u}.models φ) := by
  have value : ev (lowerSetsHeads (L := L) large ground ν) consts (trTerm (embed φ)) Fin.elim0 =
      truthCode (ZFSetHOLTypeInterpretation.holds (interpret constants.{u} φ emptyValuation)) :=
    (ev_trTerm_embed large reads φ emptyValuation).trans (prop_val _)
  rw [ev_cHolds reads value]
  congr 1
  exact propext (holds_interpret_core_iff φ)

variable (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
  (univOf large) consts)

include reads

/-- **The proofs of a closed statement**: the value of the type of the proofs of its term is
the truth value of the statement in the model of the logic. -/
theorem ev_holds_trTerm (φ : ClosedFormula UniverseSymbol) :
    ev (lowerSetsHeads (L := L) large ground ν) consts (cHolds (trTerm φ)) Fin.elim0 =
      truthCode ((universeModel small).models φ) := by
  have value : ev (lowerSetsHeads (L := L) large ground ν) consts (trTerm φ) Fin.elim0 =
      truthCode (ZFSetHOLTypeInterpretation.holds
        (interpret (universeConstants small) φ emptyValuation)) :=
    (ev_trTerm small large reads φ emptyValuation).trans (prop_val _)
  rw [ev_cHolds reads value]
  congr 1
  exact propext (holds_interpret_iff small φ)

/-- **A closed statement is true in the model of the logic exactly when its term has a proof
in the model of the package**, the empty set. -/
theorem empty_mem_holds_trTerm_iff (φ : ClosedFormula UniverseSymbol) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
        (cHolds (trTerm φ)) Fin.elim0 ↔ (universeModel small).models φ := by
  rw [ev_holds_trTerm small large reads, Square.square_truth_iff]

/-- A closed statement that is false in the model of the logic has no proof in the model of
the package. -/
theorem notMem_holds_trTerm {φ : ClosedFormula UniverseSymbol}
    (false : ¬ (universeModel small).models φ) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts (cHolds (trTerm φ)) Fin.elim0 := by
  intro inside
  rw [ev_holds_trTerm small large reads] at inside
  exact false ((mem_truthCode _ _).mp inside).2

end Truth

/-! ## The eleven laws are true in the model -/

section Laws

open ZFSetHenkinInterpretation (extensionality emptyLaw unionLaw powerLaw separationLaw
  replacementLaw setInduction extensionality_valid emptyLaw_valid unionLaw_valid powerLaw_valid
  separationLaw_valid replacementLaw_valid setInduction_valid)
open ZFSetUniverseInterpretation (universeIn universeTransitive universeClosed universeMinimal
  universeIn_valid universeTransitive_valid universeClosed_valid universeMinimal_valid
  universeTheory universeTheory_valid)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} {ν : Nat → Above L} {consts : DeclName → ZFSet.{u + 1}}
  {around : ZFSet.{u + 1} → ZFSet.{u + 1}}

section Sets

variable (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
  around consts)

include reads

/-- A closed statement of the sets that is true in the model whose individuals are all the
sets has a proof in the model of the package: the empty set. -/
theorem holds_embed_of_valid {φ : ClosedFormula Symbol}
    (valid : ZFSetHenkinInterpretation.model.{u}.models φ) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed φ))) Fin.elim0 := by
  rw [ev_holds_embed large reads]
  exact (Square.square_truth_iff _).mpr valid

/-- **Extensionality** is true in the model: sets with the same members are equal. -/
theorem extensionality_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed extensionality))) Fin.elim0 :=
  holds_embed_of_valid large reads extensionality_valid

/-- **The law of the empty set** is true in the model: nothing is a member of it. -/
theorem emptyLaw_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed emptyLaw))) Fin.elim0 :=
  holds_embed_of_valid large reads emptyLaw_valid

/-- **The law of the union** is true in the model. -/
theorem unionLaw_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed unionLaw))) Fin.elim0 :=
  holds_embed_of_valid large reads unionLaw_valid

/-- **The law of the power set** is true in the model. -/
theorem powerLaw_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed powerLaw))) Fin.elim0 :=
  holds_embed_of_valid large reads powerLaw_valid

/-- **Separation** is true in the model, for every predicate on the sets. -/
theorem separationLaw_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed separationLaw))) Fin.elim0 :=
  holds_embed_of_valid large reads separationLaw_valid

/-- **Replacement** is true in the model, for every function on the sets. -/
theorem replacementLaw_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed replacementLaw))) Fin.elim0 :=
  holds_embed_of_valid large reads replacementLaw_valid

/-- **Induction on membership** is true in the model, for every predicate on the sets. -/
theorem setInduction_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed setInduction))) Fin.elim0 :=
  holds_embed_of_valid large reads setInduction_valid

end Sets

variable (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
  (univOf large) consts)

include small reads

/-- **A set is a member of its universe**: true in the model. -/
theorem universeIn_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm universeIn)) Fin.elim0 :=
  (empty_mem_holds_trTerm_iff small large reads _).mpr (universeIn_valid small)

/-- **The universe of a set is transitive**: true in the model. -/
theorem universeTransitive_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm universeTransitive)) Fin.elim0 :=
  (empty_mem_holds_trTerm_iff small large reads _).mpr (universeTransitive_valid small)

/-- **The universe of a set is closed** under union, power set and replacement: true in the
model. -/
theorem universeClosed_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm universeClosed)) Fin.elim0 :=
  (empty_mem_holds_trTerm_iff small large reads _).mpr (universeClosed_valid small)

/-- **The universe of a set is the least** transitive closed set with the set as a member:
true in the model. -/
theorem universeMinimal_holds :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm universeMinimal)) Fin.elim0 :=
  (empty_mem_holds_trTerm_iff small large reads _).mpr (universeMinimal_valid small)

/-- **Each of the eleven laws is true in the model of the package.** -/
theorem universeTheory_holds {φ : ClosedFormula UniverseSymbol} (member : φ ∈ universeTheory) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm φ)) Fin.elim0 :=
  (empty_mem_holds_trTerm_iff small large reads φ).mpr (universeTheory_valid small φ member)

end Laws

/-! ## Proof constants for closed statements -/

section Proofs

open ZFSetUniverseLift (univOf_mem_carrierCode)

variable (L) in
/-- **The proof constants of a list of named closed statements**: each name at the type of
the proofs of the term of its statement. -/
def proofTable (rows : List (DeclName × ClosedFormula UniverseSymbol)) :
    List (DeclName × CTm (Head L) 0) :=
  rows.map fun row => (row.1, cHolds (trTerm row.2))

variable (L) in
/-- The declarations of the proof constants. -/
def proofDecls (rows : List (DeclName × ClosedFormula UniverseSymbol)) :
    DeclName → Option (CTm (Head L) 0) :=
  tableLookup (proofTable L rows)

variable (L) in
/-- **The tower inside the sets with the constants of set theory and a proof constant for
each of a list of named closed statements.** No equation is added. -/
abbrev withProofs (rows : List (DeclName × ClosedFormula UniverseSymbol)) :=
  withFamily (setTheory L) (proofDecls L rows) ([] : List (DefiningEquation (Head L)))

omit [LevelOrder L] in
/-- What the proof constants declare at a name is the type of the proofs of a statement of a
row with the name. -/
theorem proofDecls_some {rows : List (DeclName × ClosedFormula UniverseSymbol)} {c : DeclName}
    {T : CTm (Head L) 0} (found : proofDecls L rows c = some T) :
    ∃ φ, (c, φ) ∈ rows ∧ T = cHolds (trTerm φ) := by
  obtain ⟨⟨name, φ⟩, member, same⟩ := List.mem_map.mp (tableLookup_mem found)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨φ, member, rfl⟩

/-- The package with proof constants is a package over the set theory. -/
theorem withProofs_over (rows : List (DeclName × ClosedFormula UniverseSymbol)) :
    OverSetTheory (withProofs L rows) :=
  OverSetTheory.of_sub (ChurchRulesSub.sum_left _ _)

/-- The package with proof constants contains the steps of the equations of the set
theory. -/
theorem withProofs_computes (rows : List (DeclName × ClosedFormula UniverseSymbol)) :
    StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) (withProofs L rows) :=
  (StepsWithin.sum_right (bare L) (familyChurch (rules L) (setDecls L) (setEquations L))).trans
    (StepsWithin.sum_left _ _)

/-- **A proof constant has its type**: the type of the proofs of the term of its statement,
which is a type of the least universe. -/
theorem proofConstant_typed {rows : List (DeclName × ClosedFormula UniverseSymbol)}
    {c : DeclName} {φ : ClosedFormula UniverseSymbol} (new : setDecls L c = none)
    (declared : proofDecls L rows c = some (cHolds (trTerm φ))) :
    CTyped (withProofs L rows) .nil (.const c) (cHolds (trTerm φ)) := by
  have known : (withProofs L rows).constantType c = some (cHolds (trTerm φ)) :=
    (withFamily_declared (setTheory L) ((setTheory_constantType c).trans new)).trans declared
  have typed := definition_typed (Γ := (.nil : CCtx (Head L) 0)) known
    (holds_trTerm_typed (withProofs_over rows) φ)
    ((withProofs_over (L := L) rows).contains.isUniverse (.sort _))
  rwa [CTm.liftClosed_zero] at typed

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)
  {rows : List (DeclName × ClosedFormula UniverseSymbol)}

/-- **The package with proof constants for closed statements that are true in the model of
the logic has a set model**, when their names are new: the constants of set theory at their
values and every proof constant read as the empty set. -/
theorem withProofs_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) (fresh : ∀ row ∈ rows, setDecls L row.1 = none)
    (valid : ∀ row ∈ rows, (universeModel small).models row.2) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts
        (familyConsts base (setDecls L)
          (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
            (univOf large)))
        (proofDecls L rows) fun _ => ∅)
      (withProofs L rows) :=
  family_setModel_read (setTheory L)
    (fun consts agrees => setTheory_setModel_of_agreeing (stages_closedChain small large)
      groundTyped (fun hx => univOf_mem_carrierCode small large hx) ν base consts agrees)
    (fun c declared => by
      cases found : proofDecls L rows c with
      | none => exact absurd found declared
      | some T =>
        obtain ⟨φ, member, -⟩ := proofDecls_some found
        exact (setTheory_constantType c).trans (fresh _ member))
    (fun _ => ∅)
    (fun consts agreesBase _ {c T} declared => by
      obtain ⟨φ, member, rfl⟩ := proofDecls_some declared
      have reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large) consts := fun name known =>
        (agreesBase name (by rw [setTheory_constantType]; exact known)).trans
          (familyConsts_declared known)
      exact (empty_mem_holds_trTerm_iff small large reads φ).mpr (valid _ member))
    (fun _ _ _ _ member => absurd member List.not_mem_nil)

include small large in
/-- **Consistency of the package with proof constants for true closed statements**: no closed
term proves that the empty set is a member of itself. -/
theorem withProofs_consistent (fresh : ∀ row ∈ rows, setDecls L row.1 = none)
    (valid : ∀ row ∈ rows, (universeModel small).models row.2) (t : CTm (Head L) 0) :
    ¬ CTyped (withProofs L rows) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  CDerivable.no_closed_inhabitant
    (withProofs_setModel small large (fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅) fresh valid)
    (notMem_holds_empty_in_empty
      (reads_familyConsts _ _ fun c declared => by
        cases found : proofDecls L rows c with
        | none => exact absurd found declared
        | some T =>
          obtain ⟨φ, member, -⟩ := proofDecls_some found
          exact fresh _ member)
      ZFSetUniverseLift.carrierEmpty.2) t

variable {ν}

/-- **A package that declares a proof constant for a closed statement that is false in the
model of the logic has no set model** at this reading, at any assignment that reads the
constants of set theory. -/
theorem withProofs_no_setModel_of_false {consts : DeclName → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) consts)
    {c : DeclName} {φ : ClosedFormula UniverseSymbol} (new : setDecls L c = none)
    (declared : proofDecls L rows c = some (cHolds (trTerm φ)))
    (false : ¬ (universeModel small).models φ) :
    ¬ SetModel (lowerSetsHeads (L := L) large ground ν) consts (withProofs L rows) :=
  family_no_setModel_of_empty (setTheory L) ((setTheory_constantType c).trans new) declared consts
    (notMem_holds_trTerm small large reads false)

end Proofs

/-! ## The package with the eleven laws -/

section SetLaws

open ZFSetHenkinInterpretation (extensionality emptyLaw unionLaw powerLaw separationLaw
  replacementLaw setInduction universalSet universalSet_false)
open ZFSetUniverseInterpretation (universeIn universeTransitive universeClosed universeMinimal
  universeTheory universeTheory_valid)

/-- The proof of extensionality. -/
def extensionalityN : DeclName := .str .anonymous "extensionality"
/-- The proof of the law of the empty set. -/
def emptyLawN : DeclName := .str .anonymous "emptyLaw"
/-- The proof of the law of the union. -/
def unionLawN : DeclName := .str .anonymous "unionLaw"
/-- The proof of the law of the power set. -/
def powerLawN : DeclName := .str .anonymous "powerLaw"
/-- The proof of separation. -/
def separationLawN : DeclName := .str .anonymous "separationLaw"
/-- The proof of replacement. -/
def replacementLawN : DeclName := .str .anonymous "replacementLaw"
/-- The proof of induction on membership. -/
def setInductionN : DeclName := .str .anonymous "setInduction"
/-- The proof that a set is a member of its universe. -/
def universeInN : DeclName := .str .anonymous "universeIn"
/-- The proof that the universe of a set is transitive. -/
def universeTransitiveN : DeclName := .str .anonymous "universeTransitive"
/-- The proof that the universe of a set is closed. -/
def universeClosedN : DeclName := .str .anonymous "universeClosed"
/-- The proof that the universe of a set is the least one. -/
def universeMinimalN : DeclName := .str .anonymous "universeMinimal"

/-- **The eleven laws with the names of their proofs**: the seven laws of the sets and the
four laws of the universe operation. -/
def lawRows : List (DeclName × ClosedFormula UniverseSymbol) :=
  [(extensionalityN, embed extensionality), (emptyLawN, embed emptyLaw),
    (unionLawN, embed unionLaw), (powerLawN, embed powerLaw),
    (separationLawN, embed separationLaw), (replacementLawN, embed replacementLaw),
    (setInductionN, embed setInduction), (universeInN, universeIn),
    (universeTransitiveN, universeTransitive), (universeClosedN, universeClosed),
    (universeMinimalN, universeMinimal)]

/-- The statements of the rows are the eleven laws of the logic, in their order. -/
theorem lawRows_statements : lawRows.map Prod.snd = universeTheory := rfl

variable (L) in
/-- **The tower inside the sets with the constants of set theory and the eleven laws**, each
law declared as a proof constant. -/
abbrev setLaws := withProofs L lawRows

/-- The names of the proofs are new to the constants of set theory. -/
theorem lawRows_fresh : ∀ row ∈ lawRows, setDecls L row.1 = none := by
  intro row member
  simp only [lawRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Each law is true in the model of the logic. -/
theorem lawRows_valid (small : CofinalInaccessibles.{u}) :
    ∀ row ∈ lawRows, (universeModel small).models row.2 := fun row member =>
  universeTheory_valid small row.2
    (lawRows_statements ▸ List.mem_map.mpr ⟨row, member, rfl⟩)

/-- **Each proof constant of the package has the type of the proofs of its law.** -/
theorem setLaws_typed : ∀ row ∈ lawRows,
    CTyped (setLaws L) .nil (.const row.1) (cHolds (trTerm row.2)) := by
  intro row member
  simp only [lawRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact proofConstant_typed rfl rfl

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- **The package with the eleven laws has a set model**, relative to cofinally many
inaccessible cardinals in two universes: the type of all sets is read as all the sets of the
lower universe, the constants of set theory at their values, and every proof of a law as the
empty set. -/
theorem setLaws_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts
        (familyConsts base (setDecls L)
          (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
            (univOf large)))
        (proofDecls L lawRows) fun _ => ∅)
      (setLaws L) :=
  withProofs_setModel small large ν groundTyped base lawRows_fresh (lawRows_valid small)

include small large in
/-- **Consistency of the package with the eleven laws**, relative to cofinally many
inaccessible cardinals in two universes: no closed term proves that the empty set is a member
of itself. -/
theorem setLaws_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (setLaws L) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  withProofs_consistent small large lawRows_fresh (lawRows_valid small) t

/-! ### Examples -/

variable {ν}

/-- Positive example: **the proof constant of the law of the empty set is typed in the
package**, at the type of the proofs of the law. -/
theorem emptyLaw_typed :
    CTyped (setLaws L) .nil (.const emptyLawN) (cHolds (trTerm (embed emptyLaw))) :=
  proofConstant_typed rfl rfl

omit [LevelOrder L] in
/-- The term of the law of the empty set: `all set (λ x. imp (In x Empty) falsity)`. -/
theorem trTerm_emptyLaw :
    (trTerm (embed emptyLaw) : CTm (Head L) 0) =
      cAll allSets (.lam allSets (cImp (cIn (.var 0) cEmpty) cFalse)) := rfl

omit [LevelOrder L] in
/-- The term of the law that a set is a member of its universe:
`all set (λ x. In x (UnivOf x))`. -/
theorem trTerm_universeIn :
    (trTerm universeIn : CTm (Head L) 0) =
      cAll allSets (.lam allSets (cIn (.var 0) (cUnivOf (.var 0)))) := rfl

/-- The closed statement that every set is a member of its power set. -/
def powerIn : ClosedFormula Symbol :=
  .all (ZFSetHenkinInterpretation.member (.var .vz) (.app (.const .power) (.var .vz)))

omit [LevelOrder L] in
/-- The term of the statement that every set is a member of its power set:
`all set (λ x. In x (Power x))`. -/
theorem trTerm_powerIn :
    (trTerm (embed powerIn) : CTm (Head L) 0) =
      cAll allSets (.lam allSets (cIn (.var 0) (cPower (.var 0)))) := rfl

/-- Positive example: **every set is a member of its power set**, in the model of the
package: a closed consequence of the law of the power set. -/
theorem powerIn_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (cAll allSets (.lam allSets (cIn (.var 0) (cPower (.var 0)))))) Fin.elim0 :=
  holds_embed_of_valid large reads (φ := powerIn) fun _ _ =>
    ZFSet.mem_powerset.mpr fun _ member => member

/-- The proof of the statement that there is a set of all sets. -/
def universalSetN : DeclName := .str .anonymous "universalSet"

/-- Negative example: **the statement that there is a set of all sets is false in the model
of the package**: the type of its proofs has no member. -/
theorem universalSet_false_in_model {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed universalSet))) Fin.elim0 := by
  intro inside
  rw [ev_holds_embed large reads] at inside
  exact universalSet_false ((mem_truthCode _ _).mp inside).2

/-- Negative example: **the package that declares a proof that there is a set of all sets has
no set model** at this reading, at any assignment that reads the constants of set theory. -/
theorem universalSet_no_setModel {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    ¬ SetModel (lowerSetsHeads (L := L) large ground ν) consts
      (withProofs L [(universalSetN, embed universalSet)]) :=
  family_no_setModel_of_empty (setTheory L)
    ((setTheory_constantType universalSetN).trans rfl)
    (c := universalSetN) (T := cHolds (trTerm (embed universalSet))) rfl consts
    (universalSet_false_in_model large reads)

end SetLaws

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
