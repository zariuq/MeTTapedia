import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFormals
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls

/-!
# When an open range's instance may be skipped

An HE head with an open range, as `(-> (List $t) (List $t))`, owes at each
activation the range under the instance its arguments' typings give. HE uses
that instance twice: the activation's answer is cast at it, and a tail call the
body makes is checked against it as its expected type before the callee runs
(the callee's range must meet it). CeTTa's CALL handler computes the instance
only where it is wanted (`instance_wanted`): where the range is not shown, where
a tail call meets the type its caller owes, or where an argument the instance
types is not discharged.

**What shows an open range.** CeTTa counts as showing an open range `R`
(`prepared_pure_he_range_shown`): a whole argument whose formal is `R` itself, a
symbol whose one row is `R`, both branches of an `if` (`Shown`), and also a tail
call into any head owing a structural range (`ShownC`). The first three show the
range at every instance, with no instance computed: under any instance typing the
arguments at their formals, every value they return passes HE's cast at the
range's instance (`shown_passes`). A tail call shows the range only through the
meet of the callee's range with the activation's instance, which is exactly what
skipping the instance removes.

**Refutation.** With `(: g (-> (List $u) (List Number)))`,
`(: f (-> (List $t) (List $t)))`, `(= (f $l) (g $l))`, `(: SL (List String))` and
`(: u (-> (List String) %Undefined%))`, `(= (u $l) (f $l))`: `f`'s range is
shown by its tail call into `g`, and the argument of `u`'s call of `f` is
discharged by `u`'s formal, so CeTTa skips `f`'s instance; the tail call into `g`
then meets nothing and the machine answers `g`'s value `NL`. HE answers
`(Error (g SL) (BadType (List String) (List Number)))`
(`Controls.he_answers_error`, at budget sixteen and at budget forty): `f`'s check
binds `$t` to `String` (`Controls.f_instance`), and `g`'s range `(List Number)`
fails against the owed `(List $t)` under that binding
(`Controls.g_at_instance_rejected`), while the same call owing nothing passes
(`Controls.g_unowed_accepted`) and answers `NL` (`Controls.g_answers`). At the
rule level (`tail_shown_without_meet`): the tail position is `ShownC`, not
`Shown`, and the callee's range does not meet the activation's instance.

**The fixed rule** (`skip_exact`). Where every return position is `Shown` (no
tail call), every argument at an instance formal is discharged (each member of
its typing set allows an instance of its formal), and the formals share no
variable: every such argument passes HE's check (`OpenFormals.meetsOpen_of_covers`),
the arguments are typed under one instance (`joint_instance`), and under every
instance typing them, HE's own included, every value the body returns passes the
cast at the range's instance (`shown_passes`); the body makes no tail call, so no
meet is lost. Skipping the instance then changes no answer.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenRangeInstances

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence InferredTypeSets OpenFormals

/-! ## Return positions and what shows a range -/

/-- The return positions of an HE head's equations as the shown rule reads
them: a whole argument, a symbol literal, a tail call into a head, any other
value, and both branches of an `if`. -/
inductive Ret where
  | slot (i : ℕ)
  | sym (s : String)
  | tail (g : String)
  | other
  | ite (a b : Ret)

/-- **CeTTa's shown rule at an open range** (`prepared_pure_he_range_shown`): a
whole argument whose formal is the range itself, a symbol whose one row is the
range, a tail call into a head owing a structural range (`owes`), both branches
of an `if`. -/
def ShownC (Γ : Decls) (owes : String → Bool) (Fs : List (Ty String)) (R : Ty String) : Ret → Prop
  | .slot i => Fs[i]? = some R
  | .sym s => readRows (Γ s) = [R]
  | .tail g => owes g = true
  | .other => False
  | .ite a b => ShownC Γ owes Fs R a ∧ ShownC Γ owes Fs R b

/-- **The shown rule without tail calls**: the positions that show the range at
every instance, with no instance computed. -/
def Shown (Γ : Decls) (Fs : List (Ty String)) (R : Ty String) : Ret → Prop
  | .slot i => Fs[i]? = some R
  | .sym s => readRows (Γ s) = [R]
  | .tail _ => False
  | .other => False
  | .ite a b => Shown Γ Fs R a ∧ Shown Γ Fs R b

/-- What is shown without tail calls is shown by CeTTa's rule. -/
theorem Shown.shownC {Γ : Decls} {owes : String → Bool} {Fs : List (Ty String)} {R : Ty String} :
    ∀ {p : Ret}, Shown Γ Fs R p → ShownC Γ owes Fs R p
  | .slot _, h => h
  | .sym _, h => h
  | .ite _ _, h => ⟨Shown.shownC h.1, Shown.shownC h.2⟩

/-- A shown position makes no tail call. -/
def TailFree : Ret → Prop
  | .tail _ => False
  | .ite a b => TailFree a ∧ TailFree b
  | _ => True

theorem Shown.tailFree {Γ : Decls} {Fs : List (Ty String)} {R : Ty String} :
    ∀ {p : Ret}, Shown Γ Fs R p → TailFree p
  | .slot _, _ => trivial
  | .sym _, _ => trivial
  | .ite _ _, h => ⟨Shown.tailFree h.1, Shown.tailFree h.2⟩

/-- The values the argument and symbol positions return on arguments `vs`. -/
def retVals (vs : List Atom) : Ret → Set Atom
  | .slot i => {v | vs[i]? = some v}
  | .sym s => {.symbol s}
  | .tail _ => ∅
  | .other => ∅
  | .ite a b => retVals vs a ∪ retVals vs b

/-! ## Shown positions pass at every instance -/

/-- **A shown position passes HE's cast at every instance**: under any instance
`θ` typing every argument at its formal (or the argument has no typing), every
value a `Shown` position returns has no typing or a valid typing allowing the
range under `θ`. -/
theorem shown_passes {Γ : Decls} {Fs : List (Ty String)} {R : Ty String} {vs : List Atom}
    {θ : String → Ty Empty}
    (typed : ∀ (i : ℕ) (F : Ty String) (v : Atom), Fs[i]? = some F → vs[i]? = some v →
      StaticAt (stamp Γ v) (F.bind θ)) :
    ∀ p : Ret, Shown Γ Fs R p → ∀ v ∈ retVals vs p, StaticAt (stamp Γ v) (R.bind θ)
  | .slot i, h, v, hv => typed i R v h hv
  | .sym s, h, v, hv => by
      simp only [retVals, Set.mem_singleton_iff] at hv
      subst hv
      refine .inr ⟨inst R, ?_, θ, rfl⟩
      rw [stamp_symbol]
      simp only [Shown] at h
      simp [h]
  | .ite a b, h, v, hv => by
      rcases hv with hv | hv
      · exact shown_passes typed a h.1 v hv
      · exact shown_passes typed b h.2 v hv

/-! ## One instance from formals sharing no variable -/

/-- A relation holding pairwise at members implies another. -/
theorem forall₂_imp_mem {α β : Type} {P Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → (∀ a ∈ l₁, ∀ b, P a b → Q a b) →
      List.Forall₂ Q l₁ l₂
  | [], [], .nil, _ => .nil
  | a :: _, b :: _, .cons h rest, f =>
      .cons (f a (by simp) b h) (forall₂_imp_mem rest fun a' ha' => f a' (by simp [ha']))

/-- **Arguments meeting formals that share no variable are typed under one
instance**, where each formal is checked by HE. -/
theorem joint_instance {Γ : Decls} :
    ∀ (Fs : List (Ty String)) (vs : List Atom),
      Fs.Pairwise (fun A B => ∀ x ∈ A.vars, x ∉ B.vars) →
      List.Forall₂ (fun F v => CheckedTy F ∧ MeetsOpen F (stamp Γ v)) Fs vs →
      ∃ θ : String → Ty Empty, List.Forall₂ (fun F v => StaticAt (stamp Γ v) (F.bind θ)) Fs vs
  | [], [], _, .nil => ⟨fun _ => default, .nil⟩
  | F :: Fs, v :: vs, apart, .cons ⟨checked, meets⟩ rest => by
      classical
      rw [List.pairwise_cons] at apart
      obtain ⟨θ', hrest⟩ := joint_instance Fs vs apart.2 rest
      obtain ⟨φ, hφ⟩ : ∃ φ : String → Ty Empty, StaticAt (stamp Γ v) (F.bind φ) := by
        rcases meets with h | h | ⟨φ, h⟩
        · exact ⟨fun _ => default, .inl h⟩
        · rw [checked_stamp checked] at h
          cases h
        · exact ⟨φ, .inr h⟩
      refine ⟨fun x => if x ∈ F.vars then φ x else θ' x, .cons ?_ ?_⟩
      · rwa [Ty.bind_congr F fun x hx => if_pos hx]
      · have keep : ∀ A ∈ Fs, A.bind (fun x => if x ∈ F.vars then φ x else θ' x) = A.bind θ' :=
          fun A hA => Ty.bind_congr A fun x hx => if_neg fun hF => apart.1 A hA x hF hx
        exact forall₂_imp_mem hrest fun A hA w hw => by rw [keep A hA]; exact hw

/-! ## Skipping the instance -/

/-- **Discharged arguments meet their formals**, position by position. -/
theorem meets_of_discharged {Γ : Decls} :
    ∀ {Fs : List (Ty String)} {sets : List (List (Set (Ty Empty)))} {vs : List Atom},
      List.Forall₂ (fun F Ms => ∀ S ∈ Ms, AllowsInstance F S) Fs sets →
      List.Forall₂ (fun Ms v => Covers Γ (some Ms) v) sets vs →
      List.Forall₂ (fun F v => MeetsOpen F (stamp Γ v)) Fs vs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hF rest, .cons hv rest' =>
      .cons (meetsOpen_of_covers hF hv) (meets_of_discharged rest rest')

/-- **The fixed rule: the instance is not needed** where every return position is
shown without a tail call, every argument is discharged at its formal (each
member of its typing set allows an instance of the formal) and the formals share
no variable and are checked by HE. Then every argument passes HE's check, the
arguments are typed under one instance, under every instance typing them every
returned value passes HE's cast at the range's instance, and the body makes no
tail call, so no meet with the instance is lost. -/
theorem skip_exact {Γ : Decls} {Fs : List (Ty String)} {R : Ty String} {vs : List Atom}
    {sets : List (List (Set (Ty Empty)))} {p : Ret} (shown : Shown Γ Fs R p)
    (apart : Fs.Pairwise (fun A B => ∀ x ∈ A.vars, x ∉ B.vars)) (checked : ∀ F ∈ Fs, CheckedTy F)
    (cov : List.Forall₂ (fun Ms v => Covers Γ (some Ms) v) sets vs)
    (discharged : List.Forall₂ (fun F Ms => ∀ S ∈ Ms, AllowsInstance F S) Fs sets) :
    List.Forall₂ (fun F v => MeetsOpen F (stamp Γ v)) Fs vs ∧
      (∃ θ : String → Ty Empty, List.Forall₂ (fun F v => StaticAt (stamp Γ v) (F.bind θ)) Fs vs) ∧
      (∀ θ : String → Ty Empty, List.Forall₂ (fun F v => StaticAt (stamp Γ v) (F.bind θ)) Fs vs →
        ∀ v ∈ retVals vs p, StaticAt (stamp Γ v) (R.bind θ)) ∧
      TailFree p := by
  have meets := meets_of_discharged discharged cov
  refine ⟨meets, joint_instance Fs vs apart
    (forall₂_imp_mem meets fun F hF v hv => ⟨checked F hF, hv⟩), ?_, shown.tailFree⟩
  intro θ typed
  exact shown_passes (fun i F v hF hv => forall₂_getElem? typed hF hv) p shown

/-- **A tail call shows an open range only through the meet**: CeTTa's rule
counts a tail call into a head owing a structural range as showing the range,
the rule without tail calls does not, and where the callee's closed range `Rg` is
not the activation's instance `R θ`, HE's check of the tail call against the
instance fails, which the activation can see only if it computed the instance. -/
theorem tail_shown_without_meet (Γ : Decls) (owes : String → Bool) (Fs : List (Ty String))
    (R : Ty String) (g : String) (hg : owes g = true) (Rg : Ty Empty) (θ : String → Ty Empty)
    (miss : R.bind θ ≠ Rg) :
    ShownC Γ owes Fs R (.tail g) ∧ ¬ Shown Γ Fs R (.tail g) ∧
      ¬ ∃ ψ : String → Ty Empty, (Rg.lift : Ty String).bind ψ = R.bind θ := by
  refine ⟨hg, fun h => h, ?_⟩
  rintro ⟨ψ, hψ⟩
  rw [Ty.lift_bind_ground] at hψ
  exact miss hψ.symm

/-! ## Controls: HE's interpreter on the refuting program -/

namespace Controls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter (symbol apply equation typed)
open Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls (arrowAtom answersWith)

/-- `(List x)` as an atom. -/
def listT (x : Atom) : Atom := apply "List" [x]

/-- `(-> (List $u) (List Number))`. -/
def gType : Atom := arrowAtom [listT (.var "u"), listT (symbol "Number")]

/-- `(-> (List $t) (List $t))`. -/
def fType : Atom := arrowAtom [listT (.var "t"), listT (.var "t")]

/-- `(-> (List String) %Undefined%)`. -/
def uType : Atom := arrowAtom [listT (symbol "String"), symbol "%Undefined%"]

/-- The refuting program: `f`'s open range is shown by its tail call into `g`,
whose closed range is `(List Number)`; `u` passes `f` an argument its own formal
discharges. -/
def space : Space := Space.ofList [
  typed "SL" (listT (symbol "String")),
  typed "NL" (listT (symbol "Number")),
  typed "g" gType, typed "f" fType, typed "u" uType,
  equation (apply "g" [.var "l"]) (symbol "NL"),
  equation (apply "f" [.var "l"]) (apply "g" [.var "l"]),
  equation (apply "u" [.var "l"]) (apply "f" [.var "l"])]

/-- `(Error (g SL) (BadType (List String) (List Number)))`. -/
def badG : Atom := .expression [symbol "Error", apply "g" [symbol "SL"],
  .expression [symbol "BadType", listT (symbol "String"), listT (symbol "Number")]]

/-- **`f`'s instance**: HE's check of `(f SL)` binds `$t` to `String`, at every
budget from thirty-two on. -/
theorem f_instance (extra : ℕ) :
    checkIfFunctionTypeIsApplicable (apply "f" [symbol "SL"]) fType Atom.undefinedType space
      Bindings.empty (32 + extra) = .inr [Bindings.empty.assign "t" (symbol "String")] := by
  rw [functionTypeCovered_stable (apply "f" [symbol "SL"]) fType Atom.undefinedType space
    Bindings.empty 32 extra (lookup := rawTypeLookup space) (by decide +kernel)]
  decide

/-- **The tail call owing `f`'s instance is rejected**: `g`'s range
`(List Number)` fails against `(List $t)` with `$t` bound to `String`. -/
theorem g_at_instance_rejected (extra : ℕ) :
    checkIfFunctionTypeIsApplicable (apply "g" [symbol "SL"]) gType (listT (.var "t")) space
        (Bindings.empty.assign "t" (symbol "String")) (32 + extra) =
      .inl [mkError (apply "g" [symbol "SL"]) (.badType (listT (.var "t")) (listT (symbol "Number")))] := by
  rw [functionTypeCovered_stable (apply "g" [symbol "SL"]) gType (listT (.var "t")) space
    (Bindings.empty.assign "t" (symbol "String")) 32 extra (lookup := rawTypeLookup space)
    (by decide +kernel)]
  decide

/-- **The same call owing nothing passes**: what the machine checks once it has
skipped `f`'s instance. -/
theorem g_unowed_accepted (extra : ℕ) :
    checkIfFunctionTypeIsApplicable (apply "g" [symbol "SL"]) gType Atom.undefinedType space
      Bindings.empty (32 + extra) = .inr [Bindings.empty.assign "u" (symbol "String")] := by
  rw [functionTypeCovered_stable (apply "g" [symbol "SL"]) gType Atom.undefinedType space
    Bindings.empty 32 extra (lookup := rawTypeLookup space) (by decide +kernel)]
  decide

set_option maxRecDepth 100000 in
/-- **HE answers the error**: `(u SL)` and `(f SL)` answer
`(Error (g SL) (BadType (List String) (List Number)))`, at budget sixteen and at
budget forty. -/
theorem he_answers_error :
    answersWith space (apply "u" [symbol "SL"]) 16 = [badG] ∧
      answersWith space (apply "u" [symbol "SL"]) 40 = [badG] ∧
      answersWith space (apply "f" [symbol "SL"]) 16 = [badG] ∧
      answersWith space (apply "f" [symbol "SL"]) 40 = [badG] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 100000 in
/-- **Owing nothing, the tail call's callee answers its value**: `(g SL)` answers
`NL`, the machine's answer for `(u SL)` once `f`'s instance is skipped. -/
theorem g_answers :
    answersWith space (apply "g" [symbol "SL"]) 16 = [symbol "NL"] ∧
      answersWith space (apply "g" [symbol "SL"]) 40 = [symbol "NL"] := by
  constructor <;> decide

/-- **The rule-level reading of the refutation**: `f`'s one return position is a
tail call into `g`, which owes a structural range: CeTTa's rule shows `f`'s range
there, the rule without tail calls does not, and `g`'s range `(List Number)` is
not `f`'s instance `(List String)`. -/
theorem f_tail_shown_without_meet :
    ShownC (fun _ => []) (fun h => h == "g") [.app [.sym "List", .var "t"]] (.app [.sym "List", .var "t"])
        (.tail "g") ∧
      ¬ Shown (fun _ => []) [.app [.sym "List", .var "t"]] (.app [.sym "List", .var "t"]) (.tail "g") ∧
      ¬ ∃ ψ : String → Ty Empty,
        ((Ty.app [.sym "List", .sym "Number"] : Ty Empty).lift : Ty String).bind ψ =
          (Ty.app [.sym "List", .var "t"] : Ty String).bind (fun _ => .sym "String") :=
  tail_shown_without_meet _ _ _ _ "g" rfl _ _ (by simp)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenRangeInstances
