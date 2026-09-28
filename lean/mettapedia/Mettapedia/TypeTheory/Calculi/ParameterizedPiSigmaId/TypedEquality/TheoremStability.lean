import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.TheoremDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DecoderComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package

/-!
# Declared computations are stable under the expansion of constants they do not inspect

An expansion of constants (`ConstantExpansion.expand`) replaces each constant
by a closed body. A root computation is stable under an expansion when every
step expands to a step (`RootComputation.ExpandStable`). The declared
computations of the typed judgment are stable under every expansion that fixes
the constants their rules mention:

* definitions by one equation, when the defined constant and the right-hand
  side are fixed (`definitionComputation_expandStable`);
* the identity eliminator, when its name is fixed
  (`eliminatorComputation_expandStable`);
* the computation rules of a recursor, when the recursor and the constructors
  are fixed (`iotaComputation_expandStable`);
* the equations of a structural recursion, when the function, the
  constructors and the right-hand sides are fixed
  (`recursionComputation_expandStable`);
* the decoding of proposition codes, when the decoder, implication, and every
  instance with its carrier are fixed (`decoderComputation_expandStable`);
* unions of stable computations (`union_expandStable`, `unionAll_expandStable`);
* a package extended by proposition codes, when its base is stable and the
  decoder, implication and every code with its carrier are fixed
  (`Impredicative.Codes.extend_expandStable`).

The unfolding of a published theorem fixes every other name
(`unfoldBodies_of_ne`), and every term in which its name does not occur
(`fixesTm_unfoldBodies`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality

open Normalization
open ConstantExpansion (expand constantNames)
open TelescopeAbstraction (applyClosed)

variable {Head : Type} (bodies : ConstantExpansion.Bodies Head)

/-- A root computation is stable under an expansion when every step expands to
a step. -/
def _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.RootComputation.ExpandStable
    (C : RootComputation Head) : Prop :=
  ∀ {n : Nat} {l r : Tm Head n}, C.step l r → C.step (expand bodies l) (expand bodies r)

/-- An expansion fixes the constants of a term. -/
def FixesTm {n : Nat} (t : Tm Head n) : Prop := ∀ c ∈ constantNames t, bodies c = .const c

variable {bodies}

theorem expand_const_fixed {n : Nat} {c : DeclName} (fixed : bodies c = .const c) :
    expand bodies (.const c : Tm Head n) = .const c := by
  simp only [expand, fixed]
  rfl

theorem expand_eq_self {n : Nat} {t : Tm Head n} (fixed : FixesTm bodies t) : expand bodies t = t := by
  rw [ConstantExpansion.expand_eq_of_agreement bodies (fun c => .const c) t fixed]
  exact ConstantExpansion.expand_identity t

theorem expand_appSpine {n : Nat} (f : Tm Head n) (as : List (Tm Head n)) :
    expand bodies (appSpine f as) = appSpine (expand bodies f) (as.map (expand bodies)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem expand_applyClosed {k n : Nat} :
    ∀ (Θ : Ctx Head k) (σ : Sub Head k n) (f : Tm Head n),
      expand bodies (applyClosed Θ σ f) = applyClosed Θ (fun i => expand bodies (σ i)) (expand bodies f)
  | .nil, _, _ => rfl
  | .snoc Θ _, σ, f => by
      simp only [applyClosed, expand, expand_applyClosed Θ]

theorem expand_recApp {n : Nat} {rec : DeclName} (fixed : bodies rec = .const rec)
    (pre : List (Tm Head n)) (t : Tm Head n) :
    expand bodies (recApp rec pre t) = recApp rec (pre.map (expand bodies)) (expand bodies t) := by
  simp only [recApp, expand_appSpine, expand_const_fixed fixed, List.map_append, List.map_cons,
    List.map_nil]

/-! ## Unions -/

theorem union_expandStable {first second : RootComputation Head}
    (h₁ : first.ExpandStable bodies) (h₂ : second.ExpandStable bodies) :
    (RootComputation.union first second).ExpandStable bodies := fun step =>
  step.elim (fun h => .inl (h₁ h)) (fun h => .inr (h₂ h))

theorem unionAll_expandStable :
    ∀ {cs : List (DeclName × RootComputation Head)},
      (∀ entry ∈ cs, entry.2.ExpandStable bodies) → (RootComputation.unionAll cs).ExpandStable bodies
  | [], _ => fun step => nomatch step
  | entry :: _, h =>
      union_expandStable (h entry (List.mem_cons_self ..))
        (unionAll_expandStable fun e mem => h e (List.mem_cons_of_mem _ mem))

/-! ## Definitions by one equation and the identity eliminator -/

theorem definitionComputation_expandStable {f : DeclName} {k : Nat} {Θ : Ctx Head k}
    {rhs : Tm Head k} (fixedF : bodies f = .const f) (fixedRhs : FixesTm bodies rhs) :
    (definitionComputation f Θ rhs).ExpandStable bodies := by
  rintro n l r ⟨σ, rfl, rfl⟩
  refine ⟨fun i => expand bodies (σ i), ?_, ?_⟩
  · rw [expand_applyClosed, expand_const_fixed fixedF]
  · rw [ConstantExpansion.expand_subst, expand_eq_self fixedRhs]

theorem eliminatorComputation_expandStable {J : DeclName} (fixed : bodies J = .const J) :
    (eliminatorComputation (Head := Head) J).ExpandStable bodies := by
  rintro n l r ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩
  refine ⟨expand bodies a₀, expand bodies a₁, expand bodies a₂, _, expand bodies a₄,
    expand bodies a₅, ?_, rfl⟩
  rw [expand_appSpine, expand_const_fixed fixed]
  rfl

/-! ## Recursors -/

theorem iotaComputation_expandStable {rec : DeclName} {ctors : List (DeclName × List (Normalization.Field Head))}
    (fixedRec : bodies rec = .const rec) (fixedCtors : ∀ c ∈ ctors, bodies c.1 = .const c.1) :
    (iotaComputation rec ctors).ExpandStable bodies := by
  rintro n l r ⟨p, ms, i, k, fields, args, m, hms, hi, hargs, hm, rfl, rfl⟩
  have fixedK : bodies k = .const k := fixedCtors (k, fields) (List.mem_of_getElem? hi)
  refine ⟨expand bodies p, ms.map (expand bodies), i, k, fields, args.map (expand bodies),
    expand bodies m, by rw [List.length_map, hms], hi, by rw [List.length_map, hargs],
    by rw [List.getElem?_map, hm]; rfl, ?_, ?_⟩
  · rw [expand_recApp fixedRec, expand_appSpine, expand_const_fixed fixedK]
    rfl
  · rw [expand_appSpine, List.map_append, List.map_map, ← map_recArgs]
    congr 2
    simp only [List.map_map, Function.comp_def, expand_recApp fixedRec, List.map_cons]

/-! ## Structural recursion -/

omit bodies in
theorem map_extendSub {n m : Nat} (φ : Tm Head m → Tm Head m) (ρ : Sub Head n m)
    (values : Nat → Tm Head m) :
    ∀ (b : Nat), (fun ι => φ (extendSub ρ values b ι)) =
      extendSub (fun i => φ (ρ i)) (fun l => φ (values l)) b
  | 0 => rfl
  | b + 1 => by
      funext ι
      refine Fin.cases rfl (fun i => ?_) ι
      exact congrFun (map_extendSub φ ρ values b) i

omit bodies in
theorem map_replaceScrut {m s : Nat} (φ : Tm Head m → Tm Head m) (x : Tm Head m) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => φ (replaceScrut s x d σ ι)) = replaceScrut s (φ x) d (fun i => φ (σ i))
  | 0, _ => by
      funext ι
      refine Fin.cases rfl (fun i => rfl) ι
  | d + 1, σ => by
      funext ι
      refine Fin.cases rfl (fun i => ?_) ι
      exact congrFun (map_replaceScrut φ x d (tailSub σ)) i

omit bodies in
theorem getD_of_lt {α : Type} {as : List α} {l : Nat} (d : α) (h : l < as.length) :
    as.getD l d = as[l] := by
  rw [List.getD_eq_getElem?_getD, getElem?_pos as l h]
  rfl

omit bodies in
theorem map_matchSub {m s a : Nat} (φ : Tm Head m → Tm Head m) (as : List (Tm Head m))
    (has : as.length = a) :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun ι => φ (matchSub s a as d σ ι)) = matchSub s a (as.map φ) d (fun i => φ (σ i))
  | 0, σ => by
      show (fun ι => φ (extendSub (tailSub σ) (fun l => as.getD l defaultTm) a ι)) = _
      rw [map_extendSub]
      refine extendSub_congr _ a fun l hl => ?_
      rw [getD_of_lt (as := as) (l := l) defaultTm (by omega),
        getD_of_lt (as := as.map φ) (l := l) defaultTm (by rw [List.length_map]; omega),
        List.getElem_map]
  | d + 1, σ => by
      funext ι
      refine Fin.cases rfl (fun i => ?_) ι
      exact congrFun (map_matchSub φ as has d (tailSub σ)) i

theorem expand_hypSub {f : DeclName} (fixedF : bodies f = .const f) (e : (i : Nat) → Tm Head i)
    (s d : Nat) (fields : List (Normalization.Field Head)) :
    (fun ι => expand bodies (hypSub f e s d fields ι)) = hypSub f e s d fields := by
  unfold hypSub
  rw [map_extendSub]
  have ids_fixed : (fun i => expand bodies ((ids : Sub Head (s + fields.length + d)
      (s + fields.length + d)) i)) = ids := rfl
  rw [ids_fixed]
  refine extendSub_congr _ _ fun j hj => ?_
  have inRange : (recPositions fields).getD j 0 < fields.length := by
    rw [getD_of_lt _ hj]
    exact (recPositions_spec fields j hj).1
  unfold recCall
  rw [expand_applyClosed, expand_const_fixed fixedF]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => rfl) i
  show expand bodies (callSub s fields.length d _ 0) = callSub s fields.length d _ 0
  unfold callSub
  simp only [consSub_zero, dif_pos inRange]
  rfl

theorem recursionComputation_expandStable {f : DeclName}
    {ctors : List (DeclName × List (Normalization.Field Head))}
    {e : (i : Nat) → Tm Head i} {s d : Nat}
    {body : (k : DeclName) → (fields : List (Normalization.Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)}
    (fixedF : bodies f = .const f) (fixedCtors : ∀ c ∈ ctors, bodies c.1 = .const c.1)
    (fixedBodies : ∀ c ∈ ctors, FixesTm bodies (body c.1 c.2)) :
    (recursionComputation f ctors e s d body).ExpandStable bodies := by
  rintro n l r ⟨k, fields, σ, as, mem, has, rfl, rfl⟩
  have fixedK : bodies k = .const k := fixedCtors (k, fields) mem
  refine ⟨k, fields, fun i => expand bodies (σ i), as.map (expand bodies), mem,
    by rw [List.length_map, has], ?_, ?_⟩
  · rw [expand_applyClosed, expand_const_fixed fixedF, map_replaceScrut, expand_appSpine,
      expand_const_fixed fixedK]
  · rw [ConstantExpansion.expand_subst, map_matchSub _ as has, ConstantExpansion.expand_subst,
      expand_hypSub fixedF, expand_eq_self (fixedBodies (k, fields) mem)]

/-! ## Decoding -/

theorem decoderComputation_expandStable {D : Decoders Head}
    (fixedHolds : bodies D.holds = .const D.holds) (fixedImp : bodies D.imp = .const D.imp)
    (fixedAll : ∀ {a : DeclName} {A : Tm Head 0}, D.allCarrier a = some A →
      bodies a = .const a ∧ FixesTm bodies A)
    (fixedEq : ∀ {q : DeclName} {A : Tm Head 0}, D.eqCarrier q = some A →
      bodies q = .const q ∧ FixesTm bodies A) :
    (decoderComputation D).ExpandStable bodies := by
  intro n l r step
  cases step with
  | imp p q =>
      have decoded := DecoderStep.imp (D := D) (expand bodies p) (expand bodies q)
      simp only [expand, fixedHolds, fixedImp, ConstantExpansion.expand_rename] at decoded ⊢
      exact decoded
  | all carrier f =>
      obtain ⟨fixedA, fixedCarrier⟩ := fixedAll carrier
      have decoded := DecoderStep.all carrier (expand bodies f)
      simp only [expand, fixedHolds, fixedA, ConstantExpansion.expand_rename,
        ConstantExpansion.expand_liftClosed, expand_eq_self fixedCarrier] at decoded ⊢
      exact decoded
  | eq carrier x y =>
      obtain ⟨fixedQ, fixedCarrier⟩ := fixedEq carrier
      have decoded := DecoderStep.eq carrier (expand bodies x) (expand bodies y)
      simp only [expand, fixedHolds, fixedQ, ConstantExpansion.expand_liftClosed,
        expand_eq_self fixedCarrier] at decoded ⊢
      exact decoded

/-! ## Packages extended by codes -/

namespace Impredicative.Codes

variable (K : Codes Head)

theorem codeType_isSome_of_quantifier {a : DeclName} {A : Tm Head 0}
    (carrier : K.quantifiers a = some A) : (K.codeType a).isSome := by
  unfold codeType
  split_ifs
  · rfl
  · rfl
  · rfl
  · rw [carrier]
    rfl

theorem codeType_isSome_of_equation {e : DeclName} {A : Tm Head 0}
    (carrier : K.equationCarrier e = some A) : (K.codeType e).isSome := by
  unfold codeType
  split_ifs
  · rfl
  · rfl
  · rfl
  · cases K.quantifiers e with
    | some _ => rfl
    | none =>
        simp only [carrier]
        rfl

theorem extend_constantType_isSome (base : Rules Head) {c : DeclName}
    (code : (K.codeType c).isSome) : ((K.extend base).constantType c).isSome := by
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp code
  rw [K.extend_constantType_of_code base hT]
  rfl

/-- The extension of a stable package by codes is stable under an expansion
that fixes the decoder, implication, and every code with its carrier. -/
theorem extend_expandStable {base : Rules Head} (baseStable : base.computation.ExpandStable bodies)
    (fixedHolds : bodies K.holds = .const K.holds) (fixedImp : bodies K.imp = .const K.imp)
    (fixedAll : ∀ {a : DeclName} {A : Tm Head 0}, K.quantifiers a = some A →
      bodies a = .const a ∧ FixesTm bodies A)
    (fixedEq : ∀ {e : DeclName} {A : Tm Head 0}, K.equationCarrier e = some A →
      bodies e = .const e ∧ FixesTm bodies A) :
    (K.extend base).computation.ExpandStable bodies :=
  union_expandStable baseStable (decoderComputation_expandStable fixedHolds fixedImp fixedAll fixedEq)

end Impredicative.Codes

/-! ## Unfolding a published theorem -/

theorem unfoldBodies_of_ne {name c : DeclName} {body : Tm Head 0} (distinct : c ≠ name) :
    unfoldBodies name body c = .const c :=
  if_neg distinct

theorem fixesTm_unfoldBodies {name : DeclName} {body : Tm Head 0} {n : Nat} {t : Tm Head n}
    (absent : name ∉ constantNames t) : FixesTm (unfoldBodies name body) t :=
  fun _ mem => unfoldBodies_of_ne fun same => absent (same ▸ mem)

end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
