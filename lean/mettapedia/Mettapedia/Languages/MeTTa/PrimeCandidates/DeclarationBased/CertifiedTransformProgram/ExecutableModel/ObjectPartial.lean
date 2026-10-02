import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRules
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PartialConstants

/-!
# A rigid constant on the object package

`search : num → num`, witnessed by the constant-zero function, is not declared
in the object package. Replacing it by that witness sends each root step to a
root step: a root step is a substitution instance of a rule, so the constant
may stand in an argument, while the rule's head, constructors and right-hand
side do not mention it. The extension is therefore conservative, keeps
consistency for types in which `search` does not occur, and keeps strong
normalization of typed terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open TelescopeAbstraction (applyClosed)
open Package (U0 numT eqAtTelescope transportTelescope composeTelescope jName numRecName)
open CodeModel
open Mettapedia.Logic

namespace ObjectPartial

/-! ## The constant -/

def searchN : DeclName := .mkSimple "search"

def searchType : Tower.Tm 0 := .pi numT numT

def searchWitness : Tower.Tm 0 := .lam (.const zeroN)

/-- Replace `search` by the constant-zero function and leave every other name. -/
def searchSubst (d : DeclName) : Tower.Tm 0 :=
  cond (d == searchN) searchWitness (.const d)

abbrev avoids {n : Nat} (t : Tower.Tm n) : Bool :=
  t.allConstants (fun c => !(c == searchN))

theorem searchSubst_ne {c : DeclName} (h : (c == searchN) = false) :
    searchSubst c = .const c := by
  simp only [searchSubst, h, cond_false]

theorem search_fixes (d : DeclName) (h : (!(d == searchN)) = true) :
    searchSubst d = .const d := by
  cases hb : d == searchN with
  | false => simp only [searchSubst, hb, cond_false]
  | true =>
      rw [hb] at h
      exact (Bool.false_ne_true h).elim

theorem searchSubst_anonymous : searchSubst .anonymous = .const .anonymous :=
  searchSubst_ne (by decide)

theorem search_apart :
    searchN ≠ propN ∧ searchN ≠ holdsN ∧ searchN ≠ impN ∧
      SetProfile.allInstance? searchN = none ∧ SetProfile.eqInstance? searchN = none := by
  decide

/-! ## Instantiation through the declared computations -/

theorem allConstants_rename {n m : Nat} (ρ : Ren n m) (t : Tower.Tm n) :
    avoids (Presentation.rename ρ t) = avoids t := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp only [avoids, Presentation.rename, Tm.allConstants, ihA, ihB]
  | sigma A B ihA ihB => simp only [avoids, Presentation.rename, Tm.allConstants, ihA, ihB]
  | id A a b ihA iha ihb =>
      simp only [avoids, Presentation.rename, Tm.allConstants, ihA, iha, ihb]
  | lam body ih => simp only [avoids, Presentation.rename, Tm.allConstants, ih]
  | app g a ihg iha => simp only [avoids, Presentation.rename, Tm.allConstants, ihg, iha]
  | pair a b iha ihb => simp only [avoids, Presentation.rename, Tm.allConstants, iha, ihb]
  | fst p ih => simp only [avoids, Presentation.rename, Tm.allConstants, ih]
  | snd p ih => simp only [avoids, Presentation.rename, Tm.allConstants, ih]
  | refl a ih => simp only [avoids, Presentation.rename, Tm.allConstants, ih]

theorem inst_appSpine {n : Nat} (g : Tower.Tm n) :
    ∀ as : List (Tower.Tm n),
      (appSpine g as).instConsts searchSubst =
        appSpine (g.instConsts searchSubst) (as.map (Tm.instConsts searchSubst))
  | [] => rfl
  | a :: as => inst_appSpine (.app g a) as

theorem inst_applyClosed {n m : Nat} (Θ : Tower.Ctx n) (σ : Sub Tower.Head n m)
    (t : Tower.Tm m) :
    (applyClosed Θ σ t).instConsts searchSubst =
      applyClosed Θ (fun i => (σ i).instConsts searchSubst) (t.instConsts searchSubst) := by
  induction Θ with
  | nil => rfl
  | snoc Θ _ ih =>
      simp only [applyClosed, Tm.instConsts]
      rw [ih]

theorem inst_extendSub {n m : Nat} (ρ : Sub Tower.Head n m) (values : Nat → Tower.Tm m) :
    ∀ (b : Nat),
      (fun ι => (extendSub ρ values b ι).instConsts searchSubst) =
        extendSub (fun i => (ρ i).instConsts searchSubst)
          (fun l => (values l).instConsts searchSubst) b
  | 0 => rfl
  | b + 1 => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (extendSub ρ values b i).instConsts searchSubst = extendSub _ _ b i
        exact congrFun (inst_extendSub ρ values b) i

theorem inst_getD {n : Nat} :
    ∀ (as : List (Tower.Tm n)) (l : Nat),
      (as.getD l defaultTm).instConsts searchSubst =
        (as.map (Tm.instConsts searchSubst)).getD l defaultTm
  | [], _ => by
      simp only [List.getD_nil, defaultTm, Tm.instConsts, searchSubst_anonymous, List.map_nil]
      rfl
  | _ :: _, 0 => rfl
  | _ :: as, l + 1 => inst_getD as l

theorem inst_matchSub {m s a : Nat} (as : List (Tower.Tm m)) :
    ∀ (d : Nat) (σ : Sub Tower.Head (s + 1 + d) m),
      (fun ι => (matchSub s a as d σ ι).instConsts searchSubst) =
        matchSub s a (as.map (Tm.instConsts searchSubst)) d
          (fun i => (σ i).instConsts searchSubst)
  | 0, σ => by
      show (fun ι => (extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ι).instConsts
        searchSubst) = _
      rw [inst_extendSub]
      exact congrArg (fun values =>
        extendSub (fun i => (tailSub σ i).instConsts searchSubst) values a)
        (funext fun l => inst_getD as l)
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (matchSub s a as d (tailSub σ) i).instConsts searchSubst =
          matchSub s a (as.map (Tm.instConsts searchSubst)) d
            (tailSub fun i => (σ i).instConsts searchSubst) i
        exact congrFun (inst_matchSub as d (tailSub σ)) i

theorem inst_replaceScrut {m s : Nat} (x : Tower.Tm m) :
    ∀ (d : Nat) (σ : Sub Tower.Head (s + 1 + d) m),
      (fun ι => (replaceScrut s x d σ ι).instConsts searchSubst) =
        replaceScrut s (x.instConsts searchSubst) d (fun i => (σ i).instConsts searchSubst)
  | 0, _ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · rfl
  | d + 1, σ => by
      funext ι
      refine Fin.cases ?_ (fun i => ?_) ι
      · rfl
      · show (replaceScrut s x d (tailSub σ) i).instConsts searchSubst =
          replaceScrut s (x.instConsts searchSubst) d
            (tailSub fun i => (σ i).instConsts searchSubst) i
        exact congrFun (inst_replaceScrut x d (tailSub σ)) i

theorem inst_callSub (s a d l : Nat) :
    (fun ι => (callSub (Head := Tower.Head) s a d l ι).instConsts searchSubst) =
      callSub s a d l := by
  funext ι
  refine Fin.cases ?_ (fun i => ?_) ι
  · show (if h : l < a then (.var ⟨d + (a - 1 - l), by omega⟩ : Tower.Tm (s + a + d))
        else defaultTm).instConsts searchSubst =
      if h : l < a then .var ⟨d + (a - 1 - l), by omega⟩ else defaultTm
    split
    · rfl
    · simp only [defaultTm, Tm.instConsts, searchSubst_anonymous]
      rfl
  · rfl

theorem inst_hypSub {g : DeclName} (fixName : searchSubst g = .const g)
    (e : (i : Nat) → Tower.Tm i) (s d : Nat) (fields : List CtorField) :
    (fun ι => (hypSub g e s d fields ι).instConsts searchSubst) = hypSub g e s d fields := by
  unfold hypSub
  rw [inst_extendSub]
  congr 1
  funext j
  simp only [recCall, inst_applyClosed, Tm.instConsts, fixName, inst_callSub]
  rfl

theorem inst_definition {g : DeclName} {k : Nat} {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    (fixName : searchSubst g = .const g) (fixRhs : rhs.instConsts searchSubst = rhs)
    {n : Nat} {l r : Tower.Tm n} (step : DefinitionStep g Θ rhs l r) :
    DefinitionStep g Θ rhs (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  obtain ⟨σ, rfl, rfl⟩ := step
  refine ⟨fun i => (σ i).instConsts searchSubst, ?_, ?_⟩
  · rw [inst_applyClosed]
    simp only [Tm.instConsts]
    rw [fixName]
    rfl
  · rw [Tm.instConsts_subst, fixRhs]

theorem inst_eliminator {n : Nat} {l r : Tower.Tm n}
    (step : (eliminatorComputation jName).step l r) :
    (eliminatorComputation jName).step (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl, hr⟩ := step
  have fixJ : searchSubst jName = .const jName := searchSubst_ne (by decide)
  refine ⟨Tm.instConsts searchSubst a0, Tm.instConsts searchSubst a1,
    Tm.instConsts searchSubst a2, Tm.instConsts searchSubst a3,
    Tm.instConsts searchSubst a4, Tm.instConsts searchSubst a5, ?_, ?_⟩
  · rw [inst_appSpine]
    simp only [Tm.instConsts, List.map_cons, List.map_nil]
    rw [fixJ]
    rfl
  · rw [hr]

theorem inst_recApp {n : Nat} (rec : DeclName) (fixRec : searchSubst rec = .const rec)
    (pre : List (Tower.Tm n)) (t : Tower.Tm n) :
    (recApp rec pre t).instConsts searchSubst =
      recApp rec (pre.map (Tm.instConsts searchSubst)) (t.instConsts searchSubst) := by
  simp only [recApp, inst_appSpine, List.map_append, List.map_cons, List.map_nil, Tm.instConsts]
  rw [fixRec]
  rfl

theorem search_fixCtors : ∀ entry ∈ ctors, searchSubst entry.1 = .const entry.1 := by
  intro entry mem
  rcases List.mem_cons.mp mem with h | h
  · cases h
    exact searchSubst_ne (by decide)
  · rcases List.mem_cons.mp h with h | h
    · cases h
      exact searchSubst_ne (by decide)
    · nomatch h

theorem inst_iota {n : Nat} {l r : Tower.Tm n} (step : IotaStep numRecName ctors l r) :
    IotaStep numRecName ctors (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  obtain ⟨p, ms, i, k, fields, args, mt, hms, hi, has, hm, rfl, rfl⟩ := step
  have fixRec : searchSubst numRecName = .const numRecName := searchSubst_ne (by decide)
  have fixK : searchSubst k = .const k := search_fixCtors (k, fields) (List.mem_of_getElem? hi)
  refine ⟨p.instConsts searchSubst, ms.map (Tm.instConsts searchSubst), i, k, fields,
    args.map (Tm.instConsts searchSubst), mt.instConsts searchSubst,
    by simp only [List.length_map, hms], hi, by simp only [List.length_map, has],
    by simp only [List.getElem?_map, hm, Option.map_some], ?_, ?_⟩
  · rw [inst_recApp numRecName fixRec, inst_appSpine]
    simp only [Tm.instConsts, fixK, List.map_cons]
    rfl
  · rw [inst_appSpine, List.map_append, List.map_map, ← map_recArgs, List.map_map]
    congr 1
    congr 1
    apply congrArg (fun f => List.map f (recArgs fields args))
    funext x
    simp only [Function.comp_def]
    exact inst_recApp numRecName fixRec (p :: ms) x

theorem addBody_fixed :
    ∀ entry ∈ ctors, (addBody entry.1 entry.2).instConsts searchSubst = addBody entry.1 entry.2 := by
  intro entry mem
  rcases List.mem_cons.mp mem with h | h
  · cases h
    rfl
  · rcases List.mem_cons.mp h with h | h
    · cases h
      show (Tm.app (.const sucN) (.var 0)).instConsts searchSubst = _
      simp only [Tm.instConsts]
      rw [searchSubst_ne (by decide : (sucN == searchN) = false)]
      rfl
    · nomatch h

theorem powBody_fixed :
    ∀ entry ∈ ctors, (powBody entry.1 entry.2).instConsts searchSubst = powBody entry.1 entry.2 := by
  intro entry mem
  rcases List.mem_cons.mp mem with h | h
  · cases h
    rfl
  · rcases List.mem_cons.mp h with h | h
    · cases h
      show (Tm.app (.const powerN) (Tm.app (.var 0) (.var 1))).instConsts searchSubst = _
      simp only [Tm.instConsts]
      rw [searchSubst_ne (by decide : (powerN == searchN) = false)]
      rfl
    · nomatch h

theorem iterBody_fixed :
    ∀ entry ∈ ctors, (iterBody entry.1 entry.2).instConsts searchSubst = iterBody entry.1 entry.2 := by
  intro entry mem
  rcases List.mem_cons.mp mem with h | h
  · cases h
    rfl
  · rcases List.mem_cons.mp h with h | h
    · cases h
      rfl
    · nomatch h

theorem inst_recursion {g : DeclName} {e : (i : Nat) → Tower.Tm i} {s d : Nat}
    {body : (k : DeclName) → (fields : List CtorField) →
      Tower.Tm (s + fields.length + d + (recPositions fields).length)}
    (fixName : searchSubst g = .const g)
    (fixBody : ∀ entry ∈ ctors, (body entry.1 entry.2).instConsts searchSubst = body entry.1 entry.2)
    {n : Nat} {l r : Tower.Tm n}
    (step : RecursionStep g ctors e s d body l r) :
    RecursionStep g ctors e s d body (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
  have fixK : searchSubst k = .const k := search_fixCtors (k, fields) mem
  refine ⟨k, fields, fun i => (σ i).instConsts searchSubst,
    as.map (Tm.instConsts searchSubst), mem, by simp only [List.length_map, has], ?_, ?_⟩
  · rw [inst_applyClosed, inst_replaceScrut, inst_appSpine]
    simp only [Tm.instConsts]
    rw [fixK, fixName]
    rfl
  · rw [Tm.instConsts_subst, Tm.instConsts_subst, inst_matchSub, inst_hypSub fixName,
      fixBody (k, fields) mem]

/-! ## Declared types avoid the constant -/

theorem typeAt_absent (n : Nat) (ty : HOL.Ty SetProfile.SetBase) :
    avoids (FormationSensitiveHOLInterface.typeAt SetProfile.types n ty) = true := by
  induction ty generalizing n with
  | prop =>
      simp only [FormationSensitiveHOLInterface.typeAt, SetProfile.types, liftClosed,
        Presentation.rename, avoids, Tm.allConstants]
      decide
  | base b =>
      cases b with
      | set =>
          simp only [FormationSensitiveHOLInterface.typeAt, SetProfile.types, liftClosed,
            Presentation.rename, avoids, Tm.allConstants]
          decide
      | num =>
          simp only [FormationSensitiveHOLInterface.typeAt, SetProfile.types, liftClosed,
            Presentation.rename, avoids, Tm.allConstants]
          decide
  | arr _ _ iha ihb =>
      simp only [FormationSensitiveHOLInterface.typeAt, avoids, Tm.allConstants, Bool.and_eq_true]
      exact ⟨iha n, ihb (n + 1)⟩

theorem typeTerm_absent (ty : HOL.Ty SetProfile.SetBase) : avoids (typeTerm ty) = true :=
  typeAt_absent 0 ty

theorem quantifier_term_absent {c : DeclName} {A : Tower.Tm 0}
    (h : programCodes.quantifiers c = some A) : avoids A = true := by
  simp only [programCodes] at h
  cases hi : SetProfile.allInstance? c with
  | none =>
      rw [hi] at h
      cases h
  | some ty =>
      rw [hi, Option.map_some] at h
      have hA : typeTerm ty = A := by injection h
      rw [← hA]
      exact typeTerm_absent ty

theorem equation_term_absent {c : DeclName} {A : Tower.Tm 0}
    (h : programCodes.equationCarrier c = some A) : avoids A = true := by
  simp only [Codes.equationCarrier, programCodes] at h
  cases hi : SetProfile.eqInstance? c with
  | none =>
      rw [hi] at h
      cases h
  | some ty =>
      rw [hi, Option.map_some] at h
      have hA : typeTerm ty = A := by injection h
      rw [← hA]
      exact typeTerm_absent ty

theorem allType_absent {A : Tower.Tm 0} (hA : avoids A = true) :
    avoids (programCodes.allType A) = true := by
  simp only [Codes.allType, Codes.propT, avoids, Tm.allConstants, Bool.and_eq_true]
  exact ⟨⟨hA, by decide⟩, by decide⟩

theorem eqType_absent {A : Tower.Tm 0} (hA : avoids A = true) :
    avoids (programCodes.eqType A) = true := by
  simp only [Codes.eqType, Codes.propT, avoids, Tm.allConstants, allConstants_rename,
    Bool.and_eq_true]
  exact ⟨hA, ⟨hA, by decide⟩⟩

theorem codeType_absent {c : DeclName} {T : Tower.Tm 0}
    (h : programCodes.codeType c = some T) : avoids T = true := by
  simp only [Codes.codeType] at h
  cases hp : decide (c = programCodes.prop) with
  | true =>
      rw [of_decide_eq_true hp, if_pos rfl] at h
      cases h
      simp only [avoids, Tm.allConstants]
  | false =>
      rw [if_neg (of_decide_eq_false hp)] at h
      cases hh : decide (c = programCodes.holds) with
      | true =>
          rw [of_decide_eq_true hh, if_pos rfl] at h
          cases h
          decide
      | false =>
          rw [if_neg (of_decide_eq_false hh)] at h
          cases hi : decide (c = programCodes.imp) with
          | true =>
              rw [of_decide_eq_true hi, if_pos rfl] at h
              cases h
              decide
          | false =>
              rw [if_neg (of_decide_eq_false hi)] at h
              cases hq : programCodes.quantifiers c with
              | some A =>
                  rw [hq] at h
                  cases h
                  exact allType_absent (quantifier_term_absent hq)
              | none =>
                  rw [hq] at h
                  cases he : programCodes.equationCarrier c with
                  | some A =>
                      rw [he, Option.map_some] at h
                      cases h
                      exact eqType_absent (equation_term_absent he)
                  | none =>
                      rw [he, Option.map_none] at h
                      cases h

theorem declarations_all :
    declarations.all (fun e => avoids e.2) = true := by
  decide

theorem lookup_avoids (l : List (DeclName × Tower.Tm 0))
    (ok : l.all (fun e => avoids e.2) = true) {name : DeclName} {T : Tower.Tm 0}
    (h : l.lookup name = some T) : avoids T = true := by
  induction l generalizing T with
  | nil => nomatch h
  | cons head tail ih =>
      obtain ⟨c, A⟩ := head
      simp only [List.all_cons, Bool.and_eq_true] at ok
      cases hb : name == c with
      | true =>
          rw [List.lookup_cons, hb] at h
          have hT : A = T := by injection h
          rw [← hT]
          exact ok.1
      | false =>
          rw [List.lookup_cons, hb] at h
          exact ih ok.2 h

theorem search_fresh : objectRules.constantType searchN = none := by
  have code : programCodes.codeType searchN = none := by
    obtain ⟨hp, hh, hi, ha, he⟩ := search_apart
    have hq : programCodes.quantifiers searchN = none := by
      change (SetProfile.allInstance? searchN).map typeTerm = none
      rw [ha, Option.map_none]
    have hEq : programCodes.equationCarrier searchN = none := by
      change (if true = true then (SetProfile.eqInstance? searchN).map typeTerm else none) = none
      rw [if_pos rfl, he, Option.map_none]
    have hp' : searchN ≠ programCodes.prop := by
      change searchN ≠ propN
      exact hp
    have hh' : searchN ≠ programCodes.holds := by
      change searchN ≠ holdsN
      exact hh
    have hi' : searchN ≠ programCodes.imp := by
      change searchN ≠ impN
      exact hi
    rw [Codes.codeType, if_neg hp', if_neg hh', if_neg hi']
    simp only [hq, hEq, Option.map_none]
  change (programCodes.codeType searchN).orElse (fun _ => rules.constantType searchN) = none
  rw [code]
  change rules.constantType searchN = none
  rw [rules]
  change (if true = true then allTypes searchN else none) = none
  rw [if_pos rfl, allTypes]
  decide

theorem search_typesAbsent {d : DeclName} {T : Tower.Tm 0}
    (h : objectRules.constantType d = some T) : avoids T = true := by
  cases hc : programCodes.codeType d with
  | some Tc =>
      have same : objectRules.constantType d = some Tc := by
        simp only [objectRules, Codes.extend, hc, Option.orElse]
      rw [same] at h
      have hT : Tc = T := by injection h
      rw [← hT]
      exact codeType_absent hc
  | none =>
      have hbase : rules.constantType d = some T := by
        have same : objectRules.constantType d = rules.constantType d := by
          simp only [objectRules, Codes.extend, hc, Option.orElse]
        rw [same] at h
        exact h
      have hall : allTypes d = some T := by
        simp only [rules, stage] at hbase
        exact hbase
      exact lookup_avoids declarations declarations_all hall

theorem search_typeAbsent : avoids searchType = true := by
  decide

/-! ## The witness is typed -/

theorem declared_num : objectRules.constantType numN = some U0 := rfl

theorem declared_zero : objectRules.constantType zeroN = some numT := rfl

theorem num_typed {n : Nat} {Γ : Tower.Ctx n} : Typed objectRules Γ numT U0 :=
  .const declared_num (.headType (.sort Tower.zero)) (.sort _)

theorem zero_typed {n : Nat} {Γ : Tower.Ctx n} : Typed objectRules Γ (.const zeroN) numT :=
  .const declared_zero num_typed (.sort _)

theorem searchType_typed : Typed objectRules .nil searchType U0 :=
  .cumul (.piForm num_typed (.sort _) num_typed (.sort _) (.sorts Tower.zero Tower.zero))
    (fun _ => Nat.le_of_eq (Nat.max_self _))

theorem searchWitness_typed : Typed objectRules .nil searchWitness searchType :=
  .lamIntro searchType_typed (.sort _) zero_typed

/-! ## Root steps stay root steps -/

theorem inst_decoder {n : Nat} {l r : Tower.Tm n}
    (step : DecoderStep programCodes.decoders l r) :
    DecoderStep programCodes.decoders (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  cases step with
  | imp p q =>
      have fixH : searchSubst programCodes.decoders.holds = .const programCodes.decoders.holds :=
        searchSubst_ne (by decide)
      have fixI : searchSubst programCodes.decoders.imp = .const programCodes.decoders.imp :=
        searchSubst_ne (by decide)
      simp only [Tm.instConsts, fixH, fixI, Tm.instConsts_rename]
      exact .imp _ _
  | @all a A carrier f =>
      have fixH : searchSubst programCodes.decoders.holds = .const programCodes.decoders.holds :=
        searchSubst_ne (by decide)
      have carrier' : (SetProfile.allInstance? a).map typeTerm = some A := by
        change (SetProfile.allInstance? a).map typeTerm = some A at carrier
        exact carrier
      have fixA : searchSubst a = .const a := by
        cases hb : a == searchN with
        | false => exact searchSubst_ne hb
        | true =>
            have ha : a = searchN := LawfulBEq.eq_of_beq hb
            rw [ha, search_apart.2.2.2.1, Option.map_none] at carrier'
            cases carrier'
      have quantified : programCodes.quantifiers a = some A := by
        change (SetProfile.allInstance? a).map typeTerm = some A
        exact carrier'
      have absent : (A.instConsts searchSubst) = A :=
        Tm.instConsts_of_allConstants searchSubst search_fixes (quantifier_term_absent quantified)
      simp only [Tm.instConsts, fixH, fixA, Tm.instConsts_rename, Tm.instConsts_liftClosed, absent]
      exact .all carrier _
  | @eq e A carrier x y =>
      have fixH : searchSubst programCodes.decoders.holds = .const programCodes.decoders.holds :=
        searchSubst_ne (by decide)
      have carrier' :
          (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A := by
        change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
          at carrier
        exact carrier
      have fixE : searchSubst e = .const e := by
        cases hb : e == searchN with
        | false => exact searchSubst_ne hb
        | true =>
            have heq : e = searchN := LawfulBEq.eq_of_beq hb
            rw [heq, if_pos rfl, search_apart.2.2.2.2, Option.map_none] at carrier'
            cases carrier'
      have equated : programCodes.equationCarrier e = some A := by
        change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
        exact carrier'
      have absent : (A.instConsts searchSubst) = A :=
        Tm.instConsts_of_allConstants searchSubst search_fixes (equation_term_absent equated)
      simp only [Tm.instConsts, fixH, fixE, Tm.instConsts_liftClosed, absent]
      exact .eq carrier _ _

theorem rhs_fixed {k : Nat} (rhs : Tower.Tm k) (h : avoids rhs = true) :
    rhs.instConsts searchSubst = rhs :=
  Tm.instConsts_of_allConstants searchSubst search_fixes h

theorem search_rules_stable {n : Nat} {l r : Tower.Tm n}
    (step : rules.computation.step l r) :
    rules.computation.step (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  have memKeep := mem
  rw [List.mem_filter] at mem
  obtain ⟨memC, _⟩ := mem
  rw [computations] at memC
  rcases List.mem_cons.mp memC with rfl | memC
  · exact RootComputation.step_unionAll memKeep (inst_iota h)
  · rcases List.mem_cons.mp memC with rfl | memC
    · exact RootComputation.step_unionAll memKeep
        (inst_recursion (searchSubst_ne (by decide)) addBody_fixed h)
    · rcases List.mem_cons.mp memC with rfl | memC
      · exact RootComputation.step_unionAll memKeep
          (inst_recursion (searchSubst_ne (by decide)) powBody_fixed h)
      · rcases List.mem_cons.mp memC with rfl | memC
        · exact RootComputation.step_unionAll memKeep (inst_eliminator h)
        · rcases List.mem_cons.mp memC with rfl | memC
          · exact RootComputation.step_unionAll memKeep
              (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
          · rcases List.mem_cons.mp memC with rfl | memC
            · exact RootComputation.step_unionAll memKeep
                (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
            · rcases List.mem_cons.mp memC with rfl | memC
              · exact RootComputation.step_unionAll memKeep
                  (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
              · rcases List.mem_cons.mp memC with rfl | memC
                · exact RootComputation.step_unionAll memKeep
                    (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
                · rcases List.mem_cons.mp memC with rfl | memC
                  · exact RootComputation.step_unionAll memKeep
                      (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
                  · rcases List.mem_cons.mp memC with rfl | memC
                    · exact RootComputation.step_unionAll memKeep
                        (inst_recursion (searchSubst_ne (by decide)) iterBody_fixed h)
                    · rcases List.mem_cons.mp memC with rfl | memC
                      · exact RootComputation.step_unionAll memKeep
                          (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
                      · rcases List.mem_cons.mp memC with rfl | memC
                        · exact RootComputation.step_unionAll memKeep
                            (inst_definition (searchSubst_ne (by decide)) (rhs_fixed _ (by decide)) h)
                        · nomatch memC

theorem search_stepsStable {k : Nat} {l r : Tower.Tm k}
    (step : objectRules.computation.step l r) :
    objectRules.computation.step (l.instConsts searchSubst) (r.instConsts searchSubst) := by
  rcases step with base | decoded
  · exact Or.inl (search_rules_stable base)
  · exact Or.inr (inst_decoder decoded)

/-! ## The witnessed extension -/

def searchWitnessed : Witnessed objectRules where
  name := searchN
  type := searchType
  witness := searchWitness
  fresh := search_fresh
  typesAbsent := search_typesAbsent
  stepsStable := search_stepsStable
  typeAbsent := search_typeAbsent
  universeHead := .sort Tower.zero
  universeOk := .sort _
  typeTyped := searchType_typed
  inhabited := searchWitness_typed

/-- The extended package derives `search : num → num`. -/
theorem search_typed :
    Typed (objectRules.addConstant searchN searchType) .nil (.const searchN) searchType :=
  searchWitnessed.typed_const

/-- **Conservativity.** A derivation in the extension instantiates to a derivation
of the object package, reading `search` as the constant-zero function. -/
theorem search_conserves {st : Statement Tower.Head}
    (derivation : Derivable (objectRules.addConstant searchN searchType) st) :
    Derivable objectRules (st.instConsts searchWitnessed.subst) :=
  searchWitnessed.conserves derivation

/-- A statement in which `search` does not occur is derivable in the object
package as it stands. -/
theorem search_conserves_absent {st : Statement Tower.Head}
    (absent : st.allConstants (fun n => !(n == searchN)) = true)
    (derivation : Derivable (objectRules.addConstant searchN searchType) st) :
    Derivable objectRules st :=
  searchWitnessed.conserves_absent absent derivation

/-- **Consistency is kept** wherever the object package has no closed inhabitant
of a closed type in which `search` does not occur. -/
theorem search_consistent {E : Tower.Tm 0}
    (absent : avoids E = true)
    (empty : ∀ t : Tower.Tm 0, ¬ Typed objectRules .nil t E) {t : Tower.Tm 0} :
    ¬ Typed (objectRules.addConstant searchN searchType) .nil t E :=
  searchWitnessed.consistent absent empty

/-- **Strong normalization is kept.** Typed terms of the extension are strongly
normalizing whenever typed terms of the object package are. -/
theorem search_strong_normalization
    (allSN : ∀ {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n},
      CtxFormed objectRules Γ → Typed objectRules Γ t A → StrongNormalization.SN objectRules t)
    {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed (objectRules.addConstant searchN searchType) Γ)
    (typed : Typed (objectRules.addConstant searchN searchType) Γ t A) :
    StrongNormalization.SN (objectRules.addConstant searchN searchType) t :=
  searchWitnessed.strong_normalization allSN formed typed

/-- The image of `search : num → num` is the constant-zero function, typed in
the object package. -/
theorem search_witness_image : Typed objectRules .nil searchWitness searchType := by
  have moved := searchWitnessed.conserves searchWitnessed.typed_const
  simp only [Statement.instConsts, Witnessed.subst, Ctx.instConsts, Tm.instConsts,
    beq_self_eq_true, cond_true, Tm.liftClosed_at_zero] at moved
  have typeId :
      searchWitnessed.type.instConsts searchWitnessed.subst = searchWitnessed.type :=
    Tm.instConsts_of_allConstants searchWitnessed.subst searchWitnessed.fixes
      searchWitnessed.typeAbsent
  rw [typeId] at moved
  exact moved

end ObjectPartial

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
