import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingFacts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# Induction over the admitted inductive sorts of a reading

An admitted inductive sort of a reading is a simple inductive sort of the
source, whose constructors the reading reads as the constructors of a simple
inductive type of the package, with its recursor declared at the recursor type
into the universe of proofs (`AdmittedInductive`, `AdmittedInductive.Laws`).

Its induction principle, `∀P. case₁ ⇒ ⋯ ⇒ caseₖ ⇒ ∀t. P t`
(`HOL.inductionFormula`), is read by the codes of its cases
(`term_inductionFormula`), and is realized by the recursor at the code motive
`λ t. holds (P t)`:

`λ P m₁ ⋯ mₖ t. rec (λ t. holds (P t)) m₁ ⋯ mₖ t`

(`AdmittedInductive.realization`). The decoding of the code of each case is the
recursor's case type at the code motive (`Laws.equal_holds_caseCode`), so the
realization is typed at the decoding of the code of the induction principle
(`AdmittedInductive.realization_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative

open Normalization
open Mettapedia.Logic

universe u v

variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace HOLReading

/-! ## Codes of chains, motives and cases -/

section Codes

variable (ρ : HOLReading Head Base Const)

/-- The code of `p₁ ⇒ ⋯ ⇒ q`. -/
def impChain {n : Nat} : List (Tm Head n) → Tm Head n → Tm Head n
  | [], q => q
  | p :: ps, q => ρ.impOf p (impChain ps q)

/-- The code motive `λ t. holds (P t)`. -/
def motiveOf {n : Nat} (P : Tm Head n) : Tm Head n :=
  .lam (ρ.holdsOf (.app (Presentation.rename wk P) (.var 0)))

/-- The code of the case of the constructor `k` at the motive `P`, over the
fields `xs` bound so far and the recursive ones `recs` among them. -/
def caseCode (sort : Base) (k : DeclName) :
    List (Option (HOL.Ty Base)) → {n : Nat} → Tm Head n → List (Tm Head n) →
      List (Tm Head n) → Tm Head n
  | [], _, P, xs, recs => ρ.impChain (recs.map (.app P)) (.app P (appSpine (.const k) xs))
  | none :: fields, _, P, xs, recs =>
      ρ.allOf (.base sort) (.lam (caseCode sort k fields (Presentation.rename wk P)
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk) ++ [.var 0])))
  | some σ :: fields, _, P, xs, recs =>
      ρ.allOf σ (.lam (caseCode sort k fields (Presentation.rename wk P)
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk))))

theorem rename_impChain {n m : Nat} (r : Ren n m) :
    ∀ (ps : List (Tm Head n)) (q : Tm Head n),
      Presentation.rename r (ρ.impChain ps q) =
        ρ.impChain (ps.map (Presentation.rename r)) (Presentation.rename r q)
  | [], _ => rfl
  | p :: ps, q => by
      simp only [impChain, List.map_cons, Presentation.rename, rename_impChain r ps q]

theorem rename_liftRen_wk {n m : Nat} (r : Ren n m) (t : Tm Head n) :
    Presentation.rename (liftRen r) (Presentation.rename wk t) =
      Presentation.rename wk (Presentation.rename r t) := by
  rw [rename_comp, rename_comp]
  rfl

theorem rename_motiveOf {n m : Nat} (r : Ren n m) (P : Tm Head n) :
    Presentation.rename r (ρ.motiveOf P) = ρ.motiveOf (Presentation.rename r P) := by
  simp only [motiveOf, Presentation.rename, rename_liftRen_wk]
  rfl

theorem rename_caseCode (sort : Base) (k : DeclName) :
    ∀ (fields : List (Option (HOL.Ty Base))) {n m : Nat} (r : Ren n m) (P : Tm Head n)
      (xs recs : List (Tm Head n)),
      Presentation.rename r (ρ.caseCode sort k fields P xs recs) =
        ρ.caseCode sort k fields (Presentation.rename r P) (xs.map (Presentation.rename r))
          (recs.map (Presentation.rename r))
  | [], _, _, r, P, xs, recs => by
      simp only [caseCode, rename_impChain, List.map_map, Function.comp_def, Presentation.rename,
        rename_appSpine]
  | none :: fields, _, _, r, P, xs, recs => by
      simp only [caseCode, Presentation.rename, rename_caseCode sort k fields (liftRen r),
        rename_liftRen_wk, List.map_append, List.map_map, Function.comp_def, List.map_cons,
        List.map_nil]
      rfl
  | some σ :: fields, _, _, r, P, xs, recs => by
      simp only [caseCode, Presentation.rename, rename_caseCode sort k fields (liftRen r),
        rename_liftRen_wk, List.map_append, List.map_map, Function.comp_def, List.map_cons,
        List.map_nil]
      rfl

end Codes

/-! ## Admitted inductive sorts -/

/-- An admitted simple inductive sort: the source sort, its constructors each
with the name of its constant in the package, the type constant and the
recursor of the package. -/
structure AdmittedInductive (Base : Type u) (Const : HOL.Ty Base → Type v) where
  sort : Base
  ctors : List (HOL.InductiveCtor Const sort × DeclName)
  typeName : DeclName
  recName : DeclName

namespace AdmittedInductive

variable (I : AdmittedInductive Base Const)

/-- The source induction principle. -/
def inductionFormula : HOL.Formula Const [] :=
  HOL.inductionFormula I.sort (I.ctors.map Prod.fst)

/-- A field of a constructor, in the package. -/
def nativeField (ρ : HOLReading Head Base Const) : Option (HOL.Ty Base) → Field Head
  | none => .recursive
  | some σ => .closed (ρ.carrier σ)

/-- The constructors, in the package. -/
def nativeCtors (ρ : HOLReading Head Base Const) : List (DeclName × List (Field Head)) :=
  I.ctors.map fun c => (c.2, c.1.fields.map (nativeField ρ))

/-- The laws of an admitted inductive sort: the reading reads the sort as the
type constant and each constructor as its constant, and the recursor is typed
at the recursor type into the universe of proofs. -/
structure Laws (ρ : HOLReading Head Base Const) : Prop where
  sort : ρ.sort I.sort = .const I.typeName
  ctor : ∀ c ∈ I.ctors, ρ.constant c.1.symbol = some (.const c.2)
  recursor : ∀ {n : Nat} {Γ : Ctx Head n}, Typed ρ.rules Γ (.const I.recName)
    (liftClosed (recType I.typeName ρ.codes.proofs (I.nativeCtors ρ)))

/-- The code of the cases of the listed constructors at `P`, then `∀t. P t`. -/
def chainCode (ρ : HOLReading Head Base Const) (cs : List (HOL.InductiveCtor Const I.sort × DeclName))
    {n : Nat} (P : Tm Head n) : Tm Head n :=
  ρ.impChain (cs.map fun c => ρ.caseCode I.sort c.2 c.1.fields P [] [])
    (ρ.allOf (.base I.sort) (.lam (.app (Presentation.rename wk P) (.var 0))))

/-- The code of the induction principle. -/
def code (ρ : HOLReading Head Base Const) : Tm Head 0 :=
  ρ.allOf (.arr (.base I.sort) .prop) (.lam (I.chainCode ρ I.ctors (.var 0)))

/-- The body of the realization: one abstraction for each remaining method,
then the scrutinee, where the recursor is applied to the code motive, the
methods and the scrutinee. -/
def realizationBody (ρ : HOLReading Head Base Const) : (remaining : Nat) → {n : Nat} →
    Tm Head n → List (Tm Head n) → Tm Head n
  | 0, _, P, ms =>
      .lam (recApp I.recName (ρ.motiveOf (Presentation.rename wk P) ::
        ms.map (Presentation.rename wk)) (.var 0))
  | k + 1, _, P, ms =>
      .lam (realizationBody ρ k (Presentation.rename wk P) (ms.map (Presentation.rename wk) ++ [.var 0]))

/-- `λ P m₁ ⋯ mₖ t. rec (λ t. holds (P t)) m₁ ⋯ mₖ t`. -/
def realization (ρ : HOLReading Head Base Const) : Tm Head 0 :=
  .lam (I.realizationBody ρ I.ctors.length (.var 0) [])

end AdmittedInductive

/-! ## Reading the induction principle -/

section Reading

variable (ρ : HOLReading Head Base Const)

theorem term_hypChain {Γ : HOL.Ctx Base} :
    ∀ {hs : List (HOL.Formula Const Γ)} {hs' : List (Tm Head Γ.length)} {q : HOL.Formula Const Γ}
      {q' : Tm Head Γ.length}, List.Forall₂ (fun h c => ρ.term h = some c) hs hs' →
      ρ.term q = some q' → ρ.term (HOL.hypChain hs q) = some (ρ.impChain hs' q')
  | [], [], _, _, .nil, hq => hq
  | _ :: _, _ :: _, _, _, .cons hh rest, hq => by
      simp only [HOL.hypChain, impChain, term, hh, term_hypChain rest hq]
      rfl

theorem term_caseFormula (sort : Base) (k : DeclName) :
    ∀ (fields : List (Option (HOL.Ty Base))) {Γ : HOL.Ctx Base}
      {p : HOL.Term Const Γ (.arr (.base sort) .prop)} {head : HOL.Term Const Γ (HOL.ctorType sort fields)}
      {recs : List (HOL.Term Const Γ (.base sort))} {P : Tm Head Γ.length} {xs recs' : List (Tm Head Γ.length)},
      ρ.term p = some P → ρ.term head = some (appSpine (.const k) xs) →
      List.Forall₂ (fun r c => ρ.term r = some c) recs recs' →
      ρ.term (HOL.caseFormula sort fields p head recs) = some (ρ.caseCode sort k fields P xs recs')
  | [], Γ, p, head, recs, P, xs, recs', hp, hhead, hrecs => by
      have happ : ρ.term (HOL.Term.app p head) = some (.app P (appSpine (.const k) xs)) := by
        simp only [term, hp]
        erw [hhead]
        rfl
      refine ρ.term_hypChain ?_ happ
      induction hrecs with
      | nil => exact .nil
      | cons hr _ ih => exact .cons (by simp only [term, hp, hr]; rfl) ih
  | none :: fields, Γ, p, head, recs, P, xs, recs', hp, hhead, hrecs => by
      have hp' : ρ.term (HOL.weaken (σ := .base sort) p) = some (Presentation.rename wk P) := by
        rw [ρ.term_weaken, hp]; rfl
      have hhead' : ρ.term (HOL.Term.app (HOL.weaken (σ := .base sort) head) (.var .vz)) =
          some (appSpine (.const k) (xs.map (Presentation.rename wk) ++ [.var 0])) := by
        have hw : ρ.term (HOL.weaken (σ := .base sort) head) =
            some (Presentation.rename wk (appSpine (.const k) xs)) := by
          rw [ρ.term_weaken, hhead]
          rfl
        simp only [term]
        erw [hw]
        rw [appSpine_concat, rename_appSpine]
        rfl
      have hrecs' : List.Forall₂ (fun r c => ρ.term r = some c)
          (recs.map (HOL.weaken (σ := .base sort)) ++ [.var .vz])
          (recs'.map (Presentation.rename wk) ++ [.var 0]) := by
        refine List.rel_append ?_ (.cons rfl .nil)
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact hrecs.imp fun a b h => by rw [ρ.term_weaken, h]; rfl
      simp only [HOL.caseFormula, term, term_caseFormula sort k fields hp' hhead' hrecs']
      rfl
  | some σ :: fields, Γ, p, head, recs, P, xs, recs', hp, hhead, hrecs => by
      have hp' : ρ.term (HOL.weaken (σ := σ) p) = some (Presentation.rename wk P) := by
        rw [ρ.term_weaken, hp]; rfl
      have hhead' : ρ.term (HOL.Term.app (HOL.weaken (σ := σ) head) (.var .vz)) =
          some (appSpine (.const k) (xs.map (Presentation.rename wk) ++ [.var 0])) := by
        have hw : ρ.term (HOL.weaken (σ := σ) head) =
            some (Presentation.rename wk (appSpine (.const k) xs)) := by
          rw [ρ.term_weaken, hhead]
          rfl
        simp only [term]
        erw [hw]
        rw [appSpine_concat, rename_appSpine]
        rfl
      have hrecs' : List.Forall₂ (fun r c => ρ.term r = some c)
          (recs.map (HOL.weaken (σ := σ))) (recs'.map (Presentation.rename wk)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact hrecs.imp fun a b h => by rw [ρ.term_weaken, h]; rfl
      simp only [HOL.caseFormula, term, term_caseFormula sort k fields hp' hhead' hrecs']
      rfl

/-- The code of the induction principle is read. -/
theorem term_inductionFormula (I : AdmittedInductive Base Const) (IL : I.Laws ρ) :
    ρ.term I.inductionFormula = some (I.code ρ) := by
  have cases : List.Forall₂ (fun h c => ρ.term h = some c)
      ((I.ctors.map Prod.fst).map fun c =>
        HOL.caseFormula (Γ := [.arr (.base I.sort) .prop]) I.sort c.fields (.var .vz)
          (.const c.symbol) [])
      (I.ctors.map fun c => ρ.caseCode I.sort c.2 c.1.fields (.var 0) [] []) := by
    rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun c mem => ?_
    refine ρ.term_caseFormula I.sort c.2 c.1.fields rfl ?_ .nil
    simp only [term, IL.ctor c mem, Option.map_some]
    rfl
  have concl : ρ.term (HOL.Term.all (σ := .base I.sort)
      (.app (HOL.weaken (σ := .base I.sort) (.var .vz)) (.var .vz)) : HOL.Formula Const [_]) =
      some (ρ.allOf (.base I.sort) (.lam (.app (Presentation.rename wk (.var 0)) (.var 0)))) := rfl
  simp only [AdmittedInductive.inductionFormula, HOL.inductionFormula, HOL.inductionChain, term,
    ρ.term_hypChain cases concl]
  rfl

end Reading

/-! ## Typing and decoding of the codes -/

namespace Laws

variable {ρ : HOLReading Head Base Const} (L : ρ.Laws)
include L

theorem impChain_typed {n : Nat} {Γ : Ctx Head n} :
    ∀ {ps : List (Tm Head n)} {q : Tm Head n}, (∀ p ∈ ps, Typed ρ.rules Γ p ρ.codes.propT) →
      Typed ρ.rules Γ q ρ.codes.propT → Typed ρ.rules Γ (ρ.impChain ps q) ρ.codes.propT
  | [], _, _, hq => hq
  | p :: _, _, hps, hq => L.impOf_typed (hps p (List.mem_cons_self ..))
      (impChain_typed (fun p' mem => hps p' (List.mem_cons_of_mem _ mem)) hq)

/-- The code of a case is a code. -/
theorem caseCode_typed (sort : Base) (k : DeclName) :
    ∀ (fields : List (Option (HOL.Ty Base))) {n : Nat} {Γ : Ctx Head n} {P : Tm Head n}
      {xs recs : List (Tm Head n)},
      Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base sort) .prop)) →
      Typed ρ.rules Γ (appSpine (.const k) xs) (ρ.carrierAt n (HOL.ctorType sort fields)) →
      (∀ r ∈ recs, Typed ρ.rules Γ r (ρ.carrierAt n (.base sort))) →
      Typed ρ.rules Γ (ρ.caseCode sort k fields P xs recs) ρ.codes.propT
  | [], n, Γ, P, xs, recs, hP, hhead, hrecs =>
      L.impChain_typed (fun p mem => by
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp mem
          exact app_carrier (τ := .prop) hP (hrecs r hr))
        (app_carrier (τ := .prop) hP hhead)
  | none :: fields, n, Γ, P, xs, recs, hP, hhead, hrecs => by
      refine L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed _) L.prop_typed)
        L.proofs_universe ?_)
      refine caseCode_typed sort k fields ?_ ?_ ?_
      · simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base sort))
      · have headW := hhead.weaken (extension := ρ.carrierAt n (.base sort))
        rw [rename_appSpine, rename_carrierAt] at headW
        rw [appSpine_concat]
        exact app_carrier headW (ρ.var_carrier (.base sort))
      · intro r mem
        rcases List.mem_append.mp mem with mem | mem
        · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
          simpa only [rename_carrierAt] using
            (hrecs r' hr').weaken (extension := ρ.carrierAt n (.base sort))
        · rw [List.mem_singleton] at mem
          subst mem
          exact ρ.var_carrier (.base sort)
  | some σ :: fields, n, Γ, P, xs, recs, hP, hhead, hrecs => by
      refine L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed _) L.prop_typed)
        L.proofs_universe ?_)
      refine caseCode_typed sort k fields ?_ ?_ ?_
      · simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n σ)
      · have headW := hhead.weaken (extension := ρ.carrierAt n σ)
        rw [rename_appSpine, rename_carrierAt] at headW
        rw [appSpine_concat]
        exact app_carrier headW (ρ.var_carrier σ)
      · intro r mem
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
        simpa only [rename_carrierAt] using (hrecs r' hr').weaken (extension := ρ.carrierAt n σ)

/-- The code motive is a family of proof types. -/
theorem motiveOf_typed (M : ρ.MotiveUniverse) {n : Nat} {Γ : Ctx Head n} {sort : Base}
    {P : Tm Head n} (hP : Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base sort) .prop))) :
    ∃ m, ρ.rules.isUniverse m ∧
      Typed ρ.rules Γ (.pi (ρ.carrierAt n (.base sort)) ρ.U) (.head m) ∧
      Typed ρ.rules Γ (ρ.motiveOf P) (.pi (ρ.carrierAt n (.base sort)) ρ.U) := by
  obtain ⟨m, hm, U_typed, raise, piM⟩ := M.formation
  have formed : Typed ρ.rules Γ (.pi (ρ.carrierAt n (.base sort)) ρ.U) (.head m) :=
    piM (raise (L.carrierAt_typed _)) U_typed
  have body : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort)))
      (ρ.holdsOf (.app (Presentation.rename wk P) (.var 0))) ρ.U := by
    have hP' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort))) (Presentation.rename wk P)
        (ρ.carrierAt (n + 1) (.arr (.base sort) .prop)) := by
      simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base sort))
    exact L.holdsOf_typed (app_carrier (τ := .prop) hP' (ρ.var_carrier (.base sort)))
  exact ⟨m, hm, formed, .lamIntro formed hm body⟩

/-- The code motive at a term is the decoding of the motive's code there. -/
theorem motiveOf_beta (M : ρ.MotiveUniverse) {n : Nat} {Γ : Ctx Head n} {sort : Base}
    {P a : Tm Head n} (hP : Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base sort) .prop)))
    (ha : Typed ρ.rules Γ a (ρ.carrierAt n (.base sort))) :
    Equal ρ.rules Γ (.app (ρ.motiveOf P) a) (ρ.holdsOf (.app P a)) ρ.U := by
  obtain ⟨m, hm, U_typed, raise, piM⟩ := M.formation
  have formed : Typed ρ.rules Γ (.pi (ρ.carrierAt n (.base sort)) ρ.U) (.head m) :=
    piM (raise (L.carrierAt_typed _)) U_typed
  have body : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort)))
      (ρ.holdsOf (.app (Presentation.rename wk P) (.var 0))) ρ.U := by
    have hP' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort))) (Presentation.rename wk P)
        (ρ.carrierAt (n + 1) (.arr (.base sort) .prop)) := by
      simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base sort))
    exact L.holdsOf_typed (app_carrier (τ := .prop) hP' (ρ.var_carrier (.base sort)))
  have e := Derivable.betaPi formed hm body ha
  have inst : inst0 a (ρ.holdsOf (.app (Presentation.rename wk P) (.var 0))) = ρ.holdsOf (.app P a) := by
    simp only [inst0, Presentation.subst, subst0]
    rw [← inst0, inst0_rename_wk]
    rfl
  rw [inst] at e
  exact e

/-- The decoding of `P r₁ ⇒ ⋯ ⇒ P rₖ ⇒ P h` is the recursor's case
hypotheses at the code motive. -/
theorem equal_holds_hyps (M : ρ.MotiveUniverse) {sort : Base} (k : Nat) :
    ∀ {n : Nat} {Γ : Ctx Head n} {P head : Tm Head n} {recs : List (Tm Head n)},
      recs.length = k →
      Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base sort) .prop)) →
      Typed ρ.rules Γ head (ρ.carrierAt n (.base sort)) →
      (∀ r ∈ recs, Typed ρ.rules Γ r (ρ.carrierAt n (.base sort))) →
      Equal ρ.rules Γ (ρ.holdsOf (ρ.impChain (recs.map (.app P)) (.app P head)))
        (caseHyps (ρ.motiveOf P) recs head) ρ.U := by
  induction k with
  | zero =>
      intro n Γ P head recs hlen hP hhead _
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      rw [caseHyps_nil]
      exact .symm (L.motiveOf_beta M hP hhead)
  | succ k ih =>
      intro n Γ P head recs hlen hP hhead hrecs
      cases recs with
      | nil => cases hlen
      | cons r rs =>
          have hr := hrecs r (List.mem_cons_self ..)
          have hrs : ∀ r' ∈ rs, Typed ρ.rules Γ r' (ρ.carrierAt n (.base sort)) :=
            fun r' mem => hrecs r' (List.mem_cons_of_mem _ mem)
          rw [caseHyps_cons]
          simp only [List.map_cons, impChain]
          have hPr : Typed ρ.rules Γ (.app P r) ρ.codes.propT := app_carrier (τ := .prop) hP hr
          have hRest : Typed ρ.rules Γ (ρ.impChain (rs.map (.app P)) (.app P head)) ρ.codes.propT :=
            L.impChain_typed (fun p mem => by
                obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
                exact app_carrier (τ := .prop) hP (hrs r' hr'))
              (app_carrier (τ := .prop) hP hhead)
          refine .trans (L.equal_holds_imp hPr hRest) (L.equal_pi (.symm (L.motiveOf_beta M hP hr)) ?_)
          have renamed : Presentation.rename wk (ρ.impChain (rs.map (.app P)) (.app P head)) =
              ρ.impChain ((rs.map (Presentation.rename wk)).map (.app (Presentation.rename wk P)))
                (.app (Presentation.rename wk P) (Presentation.rename wk head)) := by
            rw [ρ.rename_impChain, List.map_map, List.map_map]
            rfl
          rw [renamed, ρ.rename_motiveOf]
          refine ih (by rw [List.length_map]; simpa using hlen) ?_ ?_ ?_
          · simpa only [rename_carrierAt] using hP.weaken (extension := ρ.holdsOf (.app P r))
          · simpa only [rename_carrierAt] using hhead.weaken (extension := ρ.holdsOf (.app P r))
          · intro r' mem
            obtain ⟨r'', hr'', rfl⟩ := List.mem_map.mp mem
            simpa only [rename_carrierAt] using (hrs r'' hr'').weaken (extension := ρ.holdsOf (.app P r))

/-- **Decoding of a case.** The decoding of the code of a case is the
recursor's case type at the code motive. -/
theorem equal_holds_caseCode (M : ρ.MotiveUniverse) {sort : Base} {T k : DeclName}
    (hsort : ρ.sort sort = .const T) :
    ∀ (fields : List (Option (HOL.Ty Base))) {n : Nat} {Γ : Ctx Head n} {P : Tm Head n}
      {xs recs : List (Tm Head n)},
      Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base sort) .prop)) →
      Typed ρ.rules Γ (appSpine (.const k) xs) (ρ.carrierAt n (HOL.ctorType sort fields)) →
      (∀ r ∈ recs, Typed ρ.rules Γ r (ρ.carrierAt n (.base sort))) →
      Equal ρ.rules Γ (ρ.holdsOf (ρ.caseCode sort k fields P xs recs))
        (caseFields T k (fields.map (AdmittedInductive.nativeField ρ)) (ρ.motiveOf P) xs recs) ρ.U
  | [], n, Γ, P, xs, recs, hP, hhead, hrecs =>
      L.equal_holds_hyps M recs.length rfl hP hhead hrecs
  | none :: fields, n, Γ, P, xs, recs, hP, hhead, hrecs => by
      have hC : ρ.carrierAt n (.base sort) = .const T := by
        simp only [carrierAt, hsort]
        rfl
      have hP' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort))) (Presentation.rename wk P)
          (ρ.carrierAt (n + 1) (.arr (.base sort) .prop)) := by
        simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base sort))
      have hhead' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort)))
          (appSpine (.const k) (xs.map (Presentation.rename wk) ++ [.var 0]))
          (ρ.carrierAt (n + 1) (HOL.ctorType sort fields)) := by
        have headW := hhead.weaken (extension := ρ.carrierAt n (.base sort))
        rw [rename_appSpine, rename_carrierAt] at headW
        rw [appSpine_concat]
        exact app_carrier headW (ρ.var_carrier (.base sort))
      have hrecs' : ∀ r ∈ recs.map (Presentation.rename wk) ++ [.var 0],
          Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base sort))) r (ρ.carrierAt (n + 1) (.base sort)) := by
        intro r mem
        rcases List.mem_append.mp mem with mem | mem
        · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
          simpa only [rename_carrierAt] using
            (hrecs r' hr').weaken (extension := ρ.carrierAt n (.base sort))
        · rw [List.mem_singleton] at mem
          subst mem
          exact ρ.var_carrier (.base sort)
      have hB := L.caseCode_typed sort k fields hP' hhead' hrecs'
      refine .trans (L.equal_holds_all_lam hB) ?_
      show Equal ρ.rules Γ _ (.pi (.const T) (caseFields T k (fields.map (AdmittedInductive.nativeField ρ))
        (Presentation.rename wk (ρ.motiveOf P)) (xs.map (Presentation.rename wk) ++ [.var 0])
        (recs.map (Presentation.rename wk) ++ [.var 0]))) ρ.U
      rw [ρ.rename_motiveOf]
      exact L.equal_pi (hC ▸ .refl (L.carrierAt_typed (.base sort)))
        (equal_holds_caseCode M hsort fields hP' hhead' hrecs')
  | some σ :: fields, n, Γ, P, xs, recs, hP, hhead, hrecs => by
      have hP' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ)) (Presentation.rename wk P)
          (ρ.carrierAt (n + 1) (.arr (.base sort) .prop)) := by
        simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n σ)
      have hhead' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ))
          (appSpine (.const k) (xs.map (Presentation.rename wk) ++ [.var 0]))
          (ρ.carrierAt (n + 1) (HOL.ctorType sort fields)) := by
        have headW := hhead.weaken (extension := ρ.carrierAt n σ)
        rw [rename_appSpine, rename_carrierAt] at headW
        rw [appSpine_concat]
        exact app_carrier headW (ρ.var_carrier σ)
      have hrecs' : ∀ r ∈ recs.map (Presentation.rename wk),
          Typed ρ.rules (.snoc Γ (ρ.carrierAt n σ)) r (ρ.carrierAt (n + 1) (.base sort)) := by
        intro r mem
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp mem
        simpa only [rename_carrierAt] using (hrecs r' hr').weaken (extension := ρ.carrierAt n σ)
      have hB := L.caseCode_typed sort k fields hP' hhead' hrecs'
      refine .trans (L.equal_holds_all_lam hB) ?_
      show Equal ρ.rules Γ _ (.pi (liftClosed (ρ.carrier σ)) (caseFields T k
        (fields.map (AdmittedInductive.nativeField ρ)) (Presentation.rename wk (ρ.motiveOf P))
        (xs.map (Presentation.rename wk) ++ [.var 0]) (recs.map (Presentation.rename wk)))) ρ.U
      rw [ρ.rename_motiveOf, ρ.liftClosed_carrier]
      exact L.equal_pi (.refl (L.carrierAt_typed σ))
        (equal_holds_caseCode M hsort fields hP' hhead' hrecs')

end Laws

namespace AdmittedInductive

variable (I : AdmittedInductive Base Const) {ρ : HOLReading Head Base Const}

theorem rename_chainCode {n m : Nat} (r : Ren n m)
    (cs : List (HOL.InductiveCtor Const I.sort × DeclName)) (P : Tm Head n) :
    Presentation.rename r (I.chainCode ρ cs P) = I.chainCode ρ cs (Presentation.rename r P) := by
  simp only [chainCode, ρ.rename_impChain, List.map_map, Function.comp_def, ρ.rename_caseCode,
    List.map_nil]
  simp only [Presentation.rename, rename_liftRen_wk]
  rfl

theorem rename_caseType {n m : Nat} (r : Ren n m) (T k : DeclName) (fields : List (Field Head))
    (p : Tm Head n) :
    Presentation.rename r (caseType T k fields p) = caseType T k fields (Presentation.rename r p) := by
  rw [← subst_renSub, subst_caseType, subst_renSub]

variable {I}

/-- The code of the listed cases, then `∀t. P t`, is a code. -/
theorem chainCode_typed (L : ρ.Laws) (IL : I.Laws ρ)
    (cs : List (HOL.InductiveCtor Const I.sort × DeclName)) (hcs : ∀ c ∈ cs, c ∈ I.ctors)
    {n : Nat} {Γ : Ctx Head n} {P : Tm Head n}
    (hP : Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base I.sort) .prop))) :
    Typed ρ.rules Γ (I.chainCode ρ cs P) ρ.codes.propT := by
  refine L.impChain_typed (fun p mem => ?_) ?_
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp mem
    refine L.caseCode_typed I.sort c.2 c.1.fields hP ?_ (fun r mem => by cases mem)
    have typed := typed_closed (Γ := Γ) (L.const_typed c.1.symbol (IL.ctor c (hcs c hc)))
    rw [liftClosed_carrier] at typed
    exact typed
  · have hP' : Typed ρ.rules (.snoc Γ (ρ.carrierAt n (.base I.sort))) (Presentation.rename wk P)
        (ρ.carrierAt (n + 1) (.arr (.base I.sort) .prop)) := by
      simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base I.sort))
    exact L.allOf_typed (.lamIntro (L.pi_typed (L.carrierAt_typed _) L.prop_typed) L.proofs_universe
      (app_carrier (τ := .prop) hP' (ρ.var_carrier (.base I.sort))))

/-- **Typing of the realization body.** With the methods of the constructors
done so far typed at their case types over the code motive, the body is typed
at the decoding of the code of the remaining cases. -/
theorem realizationBody_typed (L : ρ.Laws) (M : ρ.MotiveUniverse) (IL : I.Laws ρ) :
    ∀ (rest done : List (HOL.InductiveCtor Const I.sort × DeclName)), done ++ rest = I.ctors →
      ∀ {n : Nat} {Γ : Ctx Head n} {P : Tm Head n} {ms : List (Tm Head n)},
        Typed ρ.rules Γ P (ρ.carrierAt n (.arr (.base I.sort) .prop)) →
        List.Forall₂ (fun c m => Typed ρ.rules Γ m
          (caseType I.typeName c.2 (c.1.fields.map (nativeField ρ)) (ρ.motiveOf P))) done ms →
        Typed ρ.rules Γ (I.realizationBody ρ rest.length P ms) (ρ.holdsOf (I.chainCode ρ rest P))
  | [], done, hsplit, n, Γ, P, ms, hP, hms => by
      rw [List.append_nil] at hsplit
      subst hsplit
      have hC : ∀ {k : Nat}, (ρ.carrierAt k (.base I.sort) : Tm Head k) = .const I.typeName := by
        intro k
        simp only [carrierAt, IL.sort]
        rfl
      let Δ : Ctx Head (n + 1) := .snoc Γ (ρ.carrierAt n (.base I.sort))
      have hP' : Typed ρ.rules Δ (Presentation.rename wk P)
          (ρ.carrierAt (n + 1) (.arr (.base I.sort) .prop)) := by
        simpa only [rename_carrierAt] using hP.weaken (extension := ρ.carrierAt n (.base I.sort))
      obtain ⟨m, hm, _, motiveTyped⟩ := L.motiveOf_typed M hP'
      have tP : Typed ρ.rules Δ (ρ.motiveOf (Presentation.rename wk P))
          (.pi (.const I.typeName) (.head ρ.codes.proofs)) := by
        rw [← hC]
        exact motiveTyped
      have tms : List.Forall₂ (fun c mt => Typed ρ.rules Δ mt
          (caseType I.typeName c.1 c.2 (ρ.motiveOf (Presentation.rename wk P))))
          (I.nativeCtors ρ) (ms.map (Presentation.rename wk)) := by
        unfold nativeCtors
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine hms.imp fun c m typed => ?_
        have weakened := typed.weaken (extension := ρ.carrierAt n (.base I.sort))
        rwa [rename_caseType, ρ.rename_motiveOf] at weakened
      have ht : Typed ρ.rules Δ (.var 0) (.const I.typeName) := by
        rw [← hC (k := n + 1)]
        exact ρ.var_carrier (.base I.sort)
      have applied := recApp_typed IL.recursor tP tms ht
      have hB : Typed ρ.rules Δ (.app (Presentation.rename wk P) (.var 0)) ρ.codes.propT :=
        app_carrier (τ := .prop) hP' (ρ.var_carrier (.base I.sort))
      have body : Typed ρ.rules Δ
          (recApp I.recName (ρ.motiveOf (Presentation.rename wk P) :: ms.map (Presentation.rename wk))
            (.var 0))
          (ρ.holdsOf (.app (Presentation.rename wk P) (.var 0))) :=
        .conv applied (L.motiveOf_beta M hP' (ρ.var_carrier (.base I.sort))) L.proofs_universe
      exact L.allIntro hB body
  | c :: rest, done, hsplit, n, Γ, P, ms, hP, hms => by
      have hc : c ∈ I.ctors := by rw [← hsplit]; simp
      have hrest : ∀ c' ∈ rest, c' ∈ I.ctors := fun c' mem => by rw [← hsplit]; simp [mem]
      have headAt : ∀ {k : Nat} {Δ : Ctx Head k}, Typed ρ.rules Δ (appSpine (.const c.2) [])
          (ρ.carrierAt k (HOL.ctorType I.sort c.1.fields)) := by
        intro k Δ
        have typed := typed_closed (Γ := Δ) (L.const_typed c.1.symbol (IL.ctor c hc))
        rw [liftClosed_carrier] at typed
        exact typed
      have hcase := L.caseCode_typed I.sort c.2 c.1.fields (recs := []) hP headAt
        (fun r mem => absurd mem List.not_mem_nil)
      have hchain := chainCode_typed L IL rest hrest hP
      have hP' : Typed ρ.rules (.snoc Γ (ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] [])))
          (Presentation.rename wk P) (ρ.carrierAt (n + 1) (.arr (.base I.sort) .prop)) := by
        simpa only [rename_carrierAt] using hP.weaken
      have method : Typed ρ.rules (.snoc Γ (ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] [])))
          (.var 0) (caseType I.typeName c.2 (c.1.fields.map (nativeField ρ))
            (ρ.motiveOf (Presentation.rename wk P))) := by
        have v := Derivable.var (R := ρ.rules)
          (Γ := .snoc Γ (ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] []))) 0
        simp only [Ctx.lookup_snoc_zero, Presentation.rename, ρ.rename_caseCode, List.map_nil] at v
        exact .conv v (L.equal_holds_caseCode M IL.sort c.1.fields hP' headAt
          (fun r mem => absurd mem List.not_mem_nil)) L.proofs_universe
      have hms' : List.Forall₂ (fun c' m => Typed ρ.rules
          (.snoc Γ (ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] []))) m
          (caseType I.typeName c'.2 (c'.1.fields.map (nativeField ρ))
            (ρ.motiveOf (Presentation.rename wk P))))
          (done ++ [c]) (ms.map (Presentation.rename wk) ++ [.var 0]) := by
        refine List.rel_append ?_ (.cons method .nil)
        rw [List.forall₂_map_right_iff]
        refine hms.imp fun c' m typed => ?_
        have weakened := typed.weaken
          (extension := ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] []))
        rwa [rename_caseType, ρ.rename_motiveOf] at weakened
      have ih := realizationBody_typed L M IL rest (done ++ [c])
        (by rw [List.append_assoc]; exact hsplit) hP' hms'
      have hb : Typed ρ.rules (.snoc Γ (ρ.holdsOf (ρ.caseCode I.sort c.2 c.1.fields P [] [])))
          (I.realizationBody ρ rest.length (Presentation.rename wk P)
            (ms.map (Presentation.rename wk) ++ [.var 0]))
          (ρ.holdsOf (Presentation.rename wk (I.chainCode ρ rest P))) := by
        rw [rename_chainCode]
        exact ih
      exact L.impIntro hcase hchain hb

/-- **Induction.** The recursor at the code motive realizes the induction
principle of an admitted inductive sort: the realization is a closed term at
the decoding of the code of the principle. -/
theorem realization_typed (L : ρ.Laws) (M : ρ.MotiveUniverse) (IL : I.Laws ρ) :
    Typed ρ.rules .nil (I.realization ρ) (ρ.holdsOf (I.code ρ)) := by
  have hP : Typed ρ.rules (.snoc .nil (ρ.carrierAt 0 (.arr (.base I.sort) .prop))) (.var 0)
      (ρ.carrierAt 1 (.arr (.base I.sort) .prop)) := ρ.var_carrier _
  exact L.allIntro (chainCode_typed L IL I.ctors (fun _ h => h) hP)
    (realizationBody_typed L M IL I.ctors [] rfl hP .nil)

end AdmittedInductive

end HOLReading

end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
