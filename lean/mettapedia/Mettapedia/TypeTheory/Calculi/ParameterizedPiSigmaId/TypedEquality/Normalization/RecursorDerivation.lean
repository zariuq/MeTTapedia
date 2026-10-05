import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallReordering
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstTelescope

/-!
# Structural recursion derived from the recursor

A definition by structural recursion on its argument at position `s` presents
each right-hand side with its recursive calls abstracted as hypotheses. It is
derivable from the recursor of the inductive type. Take the motive
`λ t. Π ȳ. C`, for the scrutinee `t` the type of the function of the arguments
after it, and for each constructor the method

`λ x₁ ⋯ xₐ. λ h₁ ⋯ h_r. λ y₁ ⋯ y_d. rhs`,

the right-hand side over the fields, the hypotheses and the later arguments.
The recursor applied to the motive and the methods satisfies every equation of
the definition, with its own recursive calls in place of the definition's: one
ι-step followed by β-steps. Because the motive quantifies over the later
arguments, a recursive call may change them, as an accumulator does.

Each method is built with one abstraction per field and per hypothesis, in the
order in which the recursor's case type binds them, so its typing follows the
case type's own construction. The right-hand side is placed by a substitution
that moves the hypotheses before the later arguments. The one side condition is
that the recursor eliminates into a universe holding the recursion's result
family.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-! ## Abstraction over the entries of an extension -/

/-- `λ` over `j` binders. -/
def lams {n : Nat} : (j : Nat) → Tm Head (n + j) → Tm Head n
  | 0, b => b
  | j + 1, b => lams j (.lam b)

/-- `Π` over the entries `entry 0, …, entry (j - 1)` of an extension, ending in
`B`. -/
def pis {n : Nat} (entry : (l : Nat) → Tm Head (n + l)) : (j : Nat) → Tm Head (n + j) → Tm Head n
  | 0, B => B
  | j + 1, B => pis entry j (.pi (entry j) B)

theorem piRange_eq_pis (e : (i : Nat) → Tm Head i) (j : Nat) :
    ∀ (d : Nat) (C : Tm Head (j + d)), piRange e j d C = pis (fun l => e (j + l)) d C
  | 0, _ => rfl
  | d + 1, C => piRange_eq_pis e j d (.pi (e (j + d)) C)

theorem subst_pis {n m : Nat} (σ : Sub Head n m) (entry : (l : Nat) → Tm Head (n + l)) :
    ∀ (j : Nat) (B : Tm Head (n + j)),
      Presentation.subst σ (pis entry j B) =
        pis (fun l => Presentation.subst (liftSubN σ l) (entry l)) j
          (Presentation.subst (liftSubN σ j) B)
  | 0, _ => rfl
  | j + 1, B => by
      show Presentation.subst σ (pis entry j (.pi (entry j) B)) = _
      rw [subst_pis σ entry j]
      rfl

section Typing

variable {R : Rules Head}

/-- Abstracting the entries of an extension, each a type where it is bound,
over a term typed at a type. -/
theorem Typed.lams (levels : LevelModel R L) {n : Nat} {Γ : Ctx Head n}
    {entry : (l : Nat) → Tm Head (n + l)} :
    ∀ (j : Nat) {t B : Tm Head (n + j)},
      (∀ l, l < j → IsType R (extendEntries Γ entry l) (entry l)) →
      IsType R (extendEntries Γ entry j) B →
      Typed R (extendEntries Γ entry j) t B →
      Typed R Γ (lams j t) (pis entry j B) ∧ IsType R Γ (pis entry j B)
  | 0, _, _, _, formedB, typing => ⟨typing, formedB⟩
  | j + 1, t, B, formed, formedB, typing => by
      obtain ⟨u, hu, tA⟩ := formed j (Nat.lt_succ_self j)
      obtain ⟨v, hv, tB⟩ := formedB
      obtain ⟨w, join⟩ := levels.join_exists hu hv
      have hw := (levels.join_level join).1
      have tPi : Typed R (extendEntries Γ entry j) (.pi (entry j) B) (.head w) :=
        .piForm tA hu tB hv join
      have lam : Typed R (extendEntries Γ entry j) (.lam t) (.pi (entry j) B) :=
        .lamIntro tPi hw typing
      exact Typed.lams levels j (fun l hl => formed l (by omega)) ⟨w, hw, tPi⟩ lam

/-- The entries and the end of a formed `Π` over an extension are types. -/
theorem IsType.pis_inv {n : Nat} {Γ : Ctx Head n} {entry : (l : Nat) → Tm Head (n + l)} :
    ∀ (j : Nat) {B : Tm Head (n + j)}, IsType R Γ (pis entry j B) →
      (∀ l, l < j → IsType R (extendEntries Γ entry l) (entry l)) ∧
        IsType R (extendEntries Γ entry j) B
  | 0, _, h => ⟨fun l hl => absurd hl (Nat.not_lt_zero _), h⟩
  | j + 1, B, h => by
      obtain ⟨earlier, last⟩ := IsType.pis_inv j h
      obtain ⟨w, _, typing⟩ := last
      obtain ⟨u, v, _, tA, hu, tB, hv, _, _⟩ := typing.generation
      refine ⟨fun l hl => ?_, ⟨v, hv, tB⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact earlier l hl
      · exact ⟨u, hu, tA⟩

/-- A typed substitution lifts under an extension, each entry substituted. -/
theorem SubstMor.liftN {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (typed : SubstMor R Γ Δ σ) (entry : (l : Nat) → Tm Head (n + l)) :
    ∀ (j : Nat), SubstMor R (extendEntries Γ entry j)
      (extendEntries Δ (fun l => Presentation.subst (liftSubN σ l) (entry l)) j) (liftSubN σ j)
  | 0 => typed
  | j + 1 => (SubstMor.liftN typed entry j).lift (entry j)

/-- Weakening past the entries of an extension is a context renaming. -/
theorem ctxRen_wkN {n : Nat} (Γ : Ctx Head n) (entry : (l : Nat) → Tm Head (n + l)) :
    ∀ (j : Nat), CtxRen Γ (extendEntries Γ entry j) (wkN j)
  | 0 => by
      intro i
      show Ctx.lookup Γ (wkN 0 i) = Presentation.rename (wkN 0) (Ctx.lookup Γ i)
      rw [wkN_zero, rename_id]
      rfl
  | j + 1 => by
      have h := CtxRen.comp (ctxRen_wkN Γ entry j) (CtxRen.wk (extendEntries Γ entry j) (entry j))
      exact h

end Typing

/-! ## Substitutions lifted past later arguments -/

theorem extendSub_congr {n m : Nat} (ρ : Sub Head n m) {values values' : Nat → Tm Head m} :
    ∀ (b : Nat), (∀ j, j < b → values j = values' j) → extendSub ρ values b = extendSub ρ values' b
  | 0, _ => rfl
  | b + 1, h => by
      show consSub (values b) (extendSub ρ values b) = consSub (values' b) (extendSub ρ values' b)
      rw [h b (Nat.lt_succ_self b), extendSub_congr ρ b (fun j hj => h j (by omega))]

theorem subst_liftSubN_rename_wkN {n m : Nat} (τ : Sub Head n m) :
    ∀ (d : Nat) (x : Tm Head n),
      Presentation.subst (liftSubN τ d) (Presentation.rename (wkN d) x) =
        Presentation.rename (wkN d) (Presentation.subst τ x)
  | 0, x => by
      show Presentation.subst τ (Presentation.rename (wkN 0) x) = _
      rw [wkN_zero, rename_id, wkN_zero, rename_id]
  | d + 1, x => by
      rw [rename_wkN_succ, rename_wkN_succ]
      show Presentation.subst (liftSub (liftSubN τ d)) (Presentation.rename wk _) = _
      rw [subst_liftSub_wk, subst_liftSubN_rename_wkN τ d x]

theorem liftSubN_comp {n m k : Nat} (τ : Sub Head m k) (σ : Sub Head n m) :
    ∀ (d : Nat), (fun i => Presentation.subst (liftSubN τ d) (liftSubN σ d i)) =
      liftSubN (fun i => Presentation.subst τ (σ i)) d
  | 0 => rfl
  | d + 1 => by
      funext i
      show Presentation.subst (liftSub (liftSubN τ d)) (liftSub (liftSubN σ d) i) =
        liftSub (liftSubN (fun i => Presentation.subst τ (σ i)) d) i
      rw [liftSub_comp_apply, liftSubN_comp τ σ d]

theorem subst_lams {n m : Nat} (τ : Sub Head n m) :
    ∀ (j : Nat) (b : Tm Head (n + j)),
      Presentation.subst τ (lams j b) = lams j (Presentation.subst (liftSubN τ j) b)
  | 0, _ => rfl
  | j + 1, b => by
      show Presentation.subst τ (lams j (.lam b)) = _
      rw [subst_lams τ j (.lam b)]
      rfl

/-! ## The recursor's motive and methods for a structural recursion -/

/-- Weakening a substitution past one new variable. -/
def wkSub {n m : Nat} (σ : Sub Head n m) : Sub Head n (m + 1) :=
  fun i => Presentation.rename wk (σ i)

/-- The motive `λ t. Π ȳ. C` of a structural recursion: for the scrutinee `t`,
the type of the function of the later arguments. It lives over the arguments
before the scrutinee. -/
def recMotive (e : (i : Nat) → Tm Head i) (s d : Nat) (C : Tm Head (s + 1 + d)) : Tm Head s :=
  .lam (piRange e (s + 1) d C)

section Methods

variable (s d : Nat) (k : DeclName) (fields : List (Field Head))
  (body : Tm Head (s + fields.length + d + (recPositions fields).length))

/-- The arguments of the telescope at the prefix `pre`, the constructor form of
the fields `xs`, and the later arguments as the variables bound last. -/
def formArgs {m : Nat} (pre : Sub Head s m) (xs : List (Tm Head m)) :
    Sub Head (s + 1 + d) (m + d) :=
  liftSubN (consSub (appSpine (.const k) xs) pre) d

/-- The variables of a right-hand side placed: the prefix `pre`, the fields
`xs`, the later arguments as the variables bound last, and the hypotheses
`hs`. -/
def placeSub {m : Nat} (pre : Sub Head s m) (xs hs : List (Tm Head m)) :
    Sub Head (s + fields.length + d + (recPositions fields).length) (m + d) :=
  extendSub (matchSub s fields.length (xs.map (Presentation.rename (wkN d))) d (formArgs s d k pre xs))
    (fun j => Presentation.rename (wkN d) (hs.getD j defaultTm)) (recPositions fields).length

/-- The method after its fields and hypotheses: the later arguments abstracted
over the placed right-hand side. -/
def methodCore {m : Nat} (pre : Sub Head s m) (xs hs : List (Tm Head m)) : Tm Head m :=
  lams d (Presentation.subst (placeSub s d k fields pre xs hs) body)

/-- The method after its fields: one abstraction for each remaining hypothesis. -/
def methodHyps : (c : Nat) → {m : Nat} → Sub Head s m → List (Tm Head m) → List (Tm Head m) →
    Tm Head m
  | 0, _, pre, xs, hs => methodCore s d k fields body pre xs hs
  | c + 1, _, pre, xs, hs =>
      .lam (methodHyps c (wkSub pre) (xs.map (Presentation.rename wk))
        (hs.map (Presentation.rename wk) ++ [.var 0]))

/-- The method: one abstraction for each remaining field, then the
hypotheses. -/
def methodFields : List (Field Head) → {m : Nat} → Sub Head s m → List (Tm Head m) → Tm Head m
  | [], _, pre, xs => methodHyps s d k fields body (recPositions fields).length pre xs []
  | _ :: fs, _, pre, xs =>
      .lam (methodFields fs (wkSub pre) (xs.map (Presentation.rename wk) ++ [.var 0]))

theorem subst_placeSub {m m' : Nat} (τ : Sub Head m m') (pre : Sub Head s m)
    (xs hs : List (Tm Head m)) :
    (fun ι => Presentation.subst (liftSubN τ d) (placeSub s d k fields pre xs hs ι)) =
      placeSub s d k fields (fun i => Presentation.subst τ (pre i)) (xs.map (Presentation.subst τ))
        (hs.map (Presentation.subst τ)) := by
  unfold placeSub
  rw [subst_extendSub_comp, subst_matchSub]
  have args : (fun i => Presentation.subst (liftSubN τ d) (formArgs s d k pre xs i)) =
      formArgs s d k (fun i => Presentation.subst τ (pre i)) (xs.map (Presentation.subst τ)) := by
    unfold formArgs
    rw [liftSubN_comp]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show Presentation.subst τ (appSpine (.const k) xs) = _
      rw [subst_appSpine]
      rfl
    · rfl
  have fieldArgs : (xs.map (Presentation.rename (wkN d))).map (Presentation.subst (liftSubN τ d)) =
      (xs.map (Presentation.subst τ)).map (Presentation.rename (wkN d)) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun x _ => subst_liftSubN_rename_wkN τ d x)
  rw [args, fieldArgs]
  congr 1
  funext j
  rw [subst_liftSubN_rename_wkN, getD_map_subst]

theorem subst_methodCore {m m' : Nat} (τ : Sub Head m m') (pre : Sub Head s m)
    (xs hs : List (Tm Head m)) :
    Presentation.subst τ (methodCore s d k fields body pre xs hs) =
      methodCore s d k fields body (fun i => Presentation.subst τ (pre i))
        (xs.map (Presentation.subst τ)) (hs.map (Presentation.subst τ)) := by
  unfold methodCore
  rw [subst_lams, subst_comp, subst_placeSub]

theorem subst_wkSub {m m' : Nat} (τ : Sub Head m m') (pre : Sub Head s m) :
    (fun i => Presentation.subst (liftSub τ) (wkSub pre i)) =
      wkSub (fun i => Presentation.subst τ (pre i)) := by
  funext i
  exact subst_liftSub_wk τ (pre i)

theorem map_subst_liftSub_wk {m m' : Nat} (τ : Sub Head m m') (xs : List (Tm Head m)) :
    (xs.map (Presentation.rename wk)).map (Presentation.subst (liftSub τ)) =
      (xs.map (Presentation.subst τ)).map (Presentation.rename wk) := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left (fun x _ => subst_liftSub_wk τ x)

theorem subst_methodHyps : ∀ (c : Nat) {m m' : Nat} (τ : Sub Head m m') (pre : Sub Head s m)
    (xs hs : List (Tm Head m)),
    Presentation.subst τ (methodHyps s d k fields body c pre xs hs) =
      methodHyps s d k fields body c (fun i => Presentation.subst τ (pre i))
        (xs.map (Presentation.subst τ)) (hs.map (Presentation.subst τ))
  | 0, _, _, τ, pre, xs, hs => subst_methodCore s d k fields body τ pre xs hs
  | c + 1, _, _, τ, pre, xs, hs => by
      show Tm.lam (Presentation.subst (liftSub τ) (methodHyps s d k fields body c _ _ _)) = _
      rw [subst_methodHyps c (liftSub τ), subst_wkSub, map_subst_liftSub_wk, List.map_append,
        map_subst_liftSub_wk]
      rfl

theorem subst_methodFields : ∀ (fs : List (Field Head)) {m m' : Nat} (τ : Sub Head m m')
    (pre : Sub Head s m) (xs : List (Tm Head m)),
    Presentation.subst τ (methodFields s d k fields body fs pre xs) =
      methodFields s d k fields body fs (fun i => Presentation.subst τ (pre i))
        (xs.map (Presentation.subst τ))
  | [], _, _, τ, pre, xs => by
      show Presentation.subst τ (methodHyps s d k fields body _ pre xs []) = _
      rw [subst_methodHyps]
      rfl
  | _ :: fs, _, _, τ, pre, xs => by
      show Tm.lam (Presentation.subst (liftSub τ) (methodFields s d k fields body fs _ _)) = _
      rw [subst_methodFields fs (liftSub τ), subst_wkSub, List.map_append, map_subst_liftSub_wk]
      rfl

/-! ## β-reduction of a method applied to its arguments -/

theorem subst0_wkSub {m : Nat} (a : Tm Head m) (pre : Sub Head s m) :
    (fun i => Presentation.subst (subst0 a) (wkSub pre i)) = pre := by
  funext i
  exact inst0_rename_wk a (pre i)

theorem map_subst0_wk {m : Nat} (a : Tm Head m) (xs : List (Tm Head m)) :
    (xs.map (Presentation.rename wk)).map (Presentation.subst (subst0 a)) = xs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id xs]
  exact List.map_congr_left (fun x _ => inst0_rename_wk a x)

variable {R : Rules Head}

theorem methodHyps_beta : ∀ (c : Nat) {m : Nat} (pre : Sub Head s m) (xs hs ihs : List (Tm Head m)),
    ihs.length = c →
    Reduces R (appSpine (methodHyps s d k fields body c pre xs hs) ihs)
      (methodCore s d k fields body pre xs (hs ++ ihs))
  | 0, _, pre, xs, hs, [], _ => by
      rw [List.append_nil]
      exact .refl
  | c + 1, _, pre, xs, hs, h :: ihs, hl => by
      have step : StepCore R.computation R.headEq
          (.app (methodHyps s d k fields body (c + 1) pre xs hs) h)
          (methodHyps s d k fields body c pre xs (hs ++ [h])) := by
        have := StepCore.betaPi (root := R.computation) (headEq := R.headEq)
          (methodHyps s d k fields body c (wkSub pre) (xs.map (Presentation.rename wk))
            (hs.map (Presentation.rename wk) ++ [.var 0])) h
        rw [inst0, subst_methodHyps, subst0_wkSub, map_subst0_wk, List.map_append,
          map_subst0_wk] at this
        exact this
      rw [appSpine_cons]
      refine (Reduces.appSpine_step step ihs).trans ?_
      have rest := methodHyps_beta c pre xs (hs ++ [h]) ihs (Nat.succ.inj hl)
      rwa [List.append_assoc, List.singleton_append] at rest

theorem methodFields_beta : ∀ (fs : List (Field Head)) {m : Nat} (pre : Sub Head s m)
    (xs as : List (Tm Head m)), as.length = fs.length →
    Reduces R (appSpine (methodFields s d k fields body fs pre xs) as)
      (methodHyps s d k fields body (recPositions fields).length pre (xs ++ as) [])
  | [], _, pre, xs, [], _ => by
      rw [List.append_nil]
      exact .refl
  | f :: fs, _, pre, xs, a :: as, hl => by
      have step : StepCore R.computation R.headEq
          (.app (methodFields s d k fields body (f :: fs) pre xs) a)
          (methodFields s d k fields body fs pre (xs ++ [a])) := by
        have := StepCore.betaPi (root := R.computation) (headEq := R.headEq)
          (methodFields s d k fields body fs (wkSub pre)
            (xs.map (Presentation.rename wk) ++ [.var 0])) a
        rw [inst0, subst_methodFields, subst0_wkSub, List.map_append, map_subst0_wk] at this
        exact this
      rw [appSpine_cons]
      refine (Reduces.appSpine_step step as).trans ?_
      have rest := methodFields_beta fs pre (xs ++ [a]) as (Nat.succ.inj hl)
      rwa [List.append_assoc, List.singleton_append] at rest

end Methods

theorem lams_beta {R : Rules Head} {m : Nat} :
    ∀ (d : Nat) (X : Tm Head (m + d)) (ys : List (Tm Head m)), ys.length = d →
      Reduces R (appSpine (lams d X) ys)
        (Presentation.subst (extendSub ids (fun j => ys.getD j defaultTm) d) X)
  | 0, X, [], _ => by
      show Reduces R X (Presentation.subst ids X)
      rw [subst_ids]
  | d + 1, X, ys, hl => by
      have hne : ys ≠ [] := by
        rintro rfl
        exact Nat.noConfusion hl
      obtain ⟨ys', y, rfl⟩ : ∃ ys' y, ys = ys' ++ [y] :=
        ⟨ys.dropLast, ys.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      have hl' : ys'.length = d := by
        rw [List.length_append] at hl
        exact Nat.succ.inj hl
      show Reduces R (appSpine (lams d (.lam X)) (ys' ++ [y])) _
      rw [appSpine_concat]
      have earlier := lams_beta (R := R) d (.lam X) ys' hl'
      have under : Reduces R (.app (appSpine (lams d (.lam X)) ys') y)
          (.app (Presentation.subst (extendSub ids (fun j => ys'.getD j defaultTm) d) (.lam X)) y) :=
        Reduces.congr (f := fun g => Tm.app g y) (fun st => .congAppFun st) earlier
      refine under.trans (Relation.ReflTransGen.single ?_)
      have beta := StepCore.betaPi (root := R.computation) (headEq := R.headEq)
        (Presentation.subst (liftSub (extendSub ids (fun j => ys'.getD j defaultTm) d)) X) y
      rw [inst0_subst_liftSub] at beta
      have values : extendSub ids (fun j => (ys' ++ [y]).getD j defaultTm) (d + 1) =
          consSub y (extendSub ids (fun j => ys'.getD j defaultTm) d) := by
        show consSub ((ys' ++ [y]).getD d defaultTm)
          (extendSub ids (fun j => (ys' ++ [y]).getD j defaultTm) d) = _
        have last : (ys' ++ [y]).getD d defaultTm = y := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl', Nat.sub_self]
          rfl
        have same : extendSub ids (fun j => (ys' ++ [y]).getD j defaultTm) d =
            extendSub ids (fun j => ys'.getD j defaultTm) d :=
          extendSub_congr ids d (fun j hj => by
            show (ys' ++ [y]).getD j defaultTm = ys'.getD j defaultTm
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by omega)])
        rw [last, same]
      rw [values]
      exact beta

/-! ## Argument lists -/

theorem argsSub_concat {m N : Nat} {l : List (Tm Head m)} (x : Tm Head m) (hl : l.length = N) :
    argsSub (N + 1) (l ++ [x]) = consSub x (argsSub N l) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show (l ++ [x]).getD (N + 1 - 1 - 0) (.const .anonymous) = x
    rw [List.getD_eq_getElem?_getD, show N + 1 - 1 - 0 = l.length by omega,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · show (l ++ [x]).getD (N + 1 - 1 - (j.val + 1)) (.const .anonymous) =
      l.getD (N - 1 - j.val) (.const .anonymous)
    have hj := j.isLt
    rw [show N + 1 - 1 - (j.val + 1) = N - 1 - j.val by omega, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]

theorem recArgs_length_eq {n : Nat} : ∀ (fs : List (Field Head)) (as : List (Tm Head n)),
    as.length = fs.length → (recArgs fs as).length = (recPositions fs).length
  | [], [], _ => rfl
  | .recursive :: fs, _ :: as, h => by
      show (recArgs fs as).length + 1 = ((recPositions fs).map (· + 1)).length + 1
      rw [List.length_map, recArgs_length_eq fs as (Nat.succ.inj h)]
  | .closed _ :: fs, _ :: as, h => by
      show (recArgs fs as).length = ((recPositions fs).map (· + 1)).length
      rw [List.length_map, recArgs_length_eq fs as (Nat.succ.inj h)]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: _, [], h => absurd h.symm (Nat.succ_ne_zero _)

theorem recArgs_eq_map {n : Nat} : ∀ (fs : List (Field Head)) (as : List (Tm Head n)),
    as.length = fs.length → recArgs fs as = (recPositions fs).map (fun l => as.getD l defaultTm)
  | [], [], _ => rfl
  | .recursive :: fs, a :: as, h => by
      show a :: recArgs fs as =
        (0 :: (recPositions fs).map (· + 1)).map (fun l => (a :: as).getD l defaultTm)
      rw [recArgs_eq_map fs as (Nat.succ.inj h), List.map_cons, List.map_map]
      rfl
  | .closed _ :: fs, a :: as, h => by
      show recArgs fs as = ((recPositions fs).map (· + 1)).map (fun l => (a :: as).getD l defaultTm)
      rw [recArgs_eq_map fs as (Nat.succ.inj h), List.map_map]
      rfl
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: _, [], h => absurd h.symm (Nat.succ_ne_zero _)

theorem recArgs_getD {n : Nat} (fs : List (Field Head)) (as : List (Tm Head n))
    (h : as.length = fs.length) (j : Nat) (hj : j < (recPositions fs).length) :
    (recArgs fs as).getD j defaultTm = as.getD ((recPositions fs).getD j 0) defaultTm := by
  rw [recArgs_eq_map fs as h, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj, getD_of_lt 0 hj]
  rfl

theorem recArgs_snoc {n : Nat} : ∀ (done : List (Field Head)) (xs : List (Tm Head n))
    (f : Field Head) (x : Tm Head n), xs.length = done.length →
    recArgs (done ++ [f]) (xs ++ [x]) = recArgs done xs ++ recArgs [f] [x]
  | [], [], _, _, _ => rfl
  | .recursive :: done, y :: xs, f, x, h => by
      show y :: recArgs (done ++ [f]) (xs ++ [x]) = y :: recArgs done xs ++ recArgs [f] [x]
      rw [recArgs_snoc done xs f x (Nat.succ.inj h)]
      rfl
  | .closed _ :: done, _ :: xs, f, x, h => by
      show recArgs (done ++ [f]) (xs ++ [x]) = recArgs done xs ++ recArgs [f] [x]
      exact recArgs_snoc done xs f x (Nat.succ.inj h)
  | [], _ :: _, _, _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, h => absurd h.symm (Nat.succ_ne_zero _)

theorem forall₂_map_self {α β : Type} {P : α → β → Prop} (f : α → β) :
    ∀ (l : List α), (∀ a ∈ l, P a (f a)) → List.Forall₂ P l (l.map f)
  | [], _ => .nil
  | a :: l, h => .cons (h a (List.mem_cons_self ..))
      (forall₂_map_self f l (fun b hb => h b (List.mem_cons_of_mem _ hb)))

section Arguments

variable {R : Rules Head}

theorem SubstMor.wk {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}
    (typed : SubstMor R Γ Δ σ) (A : Tm Head m) : SubstMor R Γ (.snoc Δ A) (wkSub σ) := by
  intro i
  have h := Typed.weaken (extension := A) (typed i)
  rw [rename_subst] at h
  exact h

/-- Arguments typed at the field types of a constructor, weakened. -/
theorem forall₂_fields_weaken {m : Nat} {Δ : Ctx Head m} {A : Tm Head m} {T : DeclName} :
    ∀ {fs : List (Field Head)} {xs : List (Tm Head m)},
      List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fs xs →
      List.Forall₂ (fun f x => Typed R (.snoc Δ A) x (liftClosed (Field.type T f))) fs
        (xs.map (Presentation.rename wk))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h rest => by
      refine .cons ?_ (forall₂_fields_weaken rest)
      have w := Typed.weaken (extension := A) h
      rwa [rename_liftClosed] at w

/-- Terms typed at applications of `p`, weakened. -/
theorem forall₂_hyps_weaken {m : Nat} {Δ : Ctx Head m} {A p : Tm Head m} :
    ∀ {rs hs : List (Tm Head m)}, List.Forall₂ (fun r h => Typed R Δ h (.app p r)) rs hs →
      List.Forall₂ (fun r h => Typed R (.snoc Δ A) h (.app (Presentation.rename wk p) r))
        (rs.map (Presentation.rename wk)) (hs.map (Presentation.rename wk))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h rest => .cons (Typed.weaken h) (forall₂_hyps_weaken rest)

/-- The recursive ones among arguments typed at the field types are typed at
the inductive type. -/
theorem recArgs_typed {m : Nat} {Δ : Ctx Head m} {T : DeclName} :
    ∀ {fs : List (Field Head)} {xs : List (Tm Head m)},
      List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fs xs →
      ∀ r ∈ recArgs fs xs, Typed R Δ r (.const T)
  | [], [], .nil => fun r hr => by
      change r ∈ ([] : List (Tm Head m)) at hr
      exact absurd hr (List.not_mem_nil)
  | .recursive :: _, x :: xs, .cons h rest => fun r hr => by
      change r ∈ x :: recArgs _ xs at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact h
      · exact recArgs_typed rest r hr
  | .closed _ :: _, _ :: _, .cons _ rest => fun r hr => recArgs_typed rest r hr

/-- A typed substitution of a constructor's telescope from typed arguments. -/
theorem substMor_ctorTele {T : DeclName} {fields : List (Field Head)} {m : Nat}
    {Δ : Ctx Head m} {xs : List (Tm Head m)}
    (typed : List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fields xs) :
    ∀ (j : Nat), j ≤ fields.length →
      SubstMor R (ofEntries (ctorEntry T fields) j) Δ (argsSub j (xs.take j))
  | 0, _ => fun i => Fin.elim0 i
  | j + 1, hj => by
      have hl : xs.length = fields.length := typed.length_eq.symm
      have hjx : j < xs.length := by omega
      rw [List.take_succ_eq_append_getElem hjx,
        argsSub_concat _ (by rw [List.length_take]; omega)]
      refine SubstMor.cons (substMor_ctorTele typed j (by omega)) ?_
      rw [ctorEntry_eq (by omega), subst_liftClosed]
      have h := forall₂_getD .recursive defaultTm typed j (by omega)
      rwa [getD_of_lt _ (by omega : j < fields.length), getD_of_lt _ hjx] at h

/-- A constructor applied to arguments typed at its field types. -/
theorem ctorApp_typed {T k : DeclName} {fields : List (Field Head)}
    (ctor : ∀ {n : Nat} {Γ : Ctx Head n}, Typed R Γ (.const k) (liftClosed (ctorType T fields)))
    {m : Nat} {Δ : Ctx Head m} {xs : List (Tm Head m)}
    (typed : List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fields xs) :
    Typed R Δ (appSpine (.const k) xs) (.const T) := by
  have hl : xs.length = fields.length := typed.length_eq.symm
  have mor := substMor_ctorTele typed fields.length (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at mor
  have h := Typed.telescope_apply (Θ := ctorTele T fields) (X := .const T) mor (ctor (Γ := Δ))
  rw [applyClosed_eq_appSpine] at h
  have args : telescopeArgs (ctorTele T fields) (argsSub fields.length xs) = xs :=
    telescopeArgs_argsSub (ctorEntry T fields) fields.length xs hl
  rw [args] at h
  exact h

end Arguments

theorem scrutOf_liftSubN {m s : Nat} (σ₀ : Sub Head (s + 1) m) :
    ∀ (d : Nat), scrutOf s d (liftSubN σ₀ d) = Presentation.rename (wkN d) (σ₀ 0)
  | 0 => by
      show σ₀ 0 = _
      rw [wkN_zero, rename_id]
  | d + 1 => by
      show scrutOf s d (tailSub (liftSub (liftSubN σ₀ d))) = _
      have e : tailSub (liftSub (liftSubN σ₀ d)) =
          fun i => Presentation.rename wk (liftSubN σ₀ d i) := rfl
      rw [e, scrutOf_rename, scrutOf_liftSubN σ₀ d, rename_wkN_succ]

theorem prefixSub_liftSubN {m s : Nat} (σ₀ : Sub Head (s + 1) m) :
    ∀ (d : Nat), prefixSub s d (liftSubN σ₀ d) =
      fun i => Presentation.rename (wkN d) (tailSub σ₀ i)
  | 0 => by
      funext i
      show tailSub σ₀ i = _
      rw [wkN_zero, rename_id]
  | d + 1 => by
      show prefixSub s d (tailSub (liftSub (liftSubN σ₀ d))) = _
      have e : tailSub (liftSub (liftSubN σ₀ d)) =
          fun i => Presentation.rename wk (liftSubN σ₀ d i) := rfl
      rw [e, prefixSub_rename, prefixSub_liftSubN σ₀ d]
      funext i
      show Presentation.rename wk (Presentation.rename (wkN d) (tailSub σ₀ i)) = _
      rw [rename_wkN_succ]

/-- The later entries of the telescope at the arguments `σ₀` of the prefix and
the scrutinee. -/
def laterEntries (e : (i : Nat) → Tm Head i) (s : Nat) {m : Nat} (σ₀ : Sub Head (s + 1) m)
    (l : Nat) : Tm Head (m + l) :=
  Presentation.subst (liftSubN σ₀ l) (e (s + 1 + l))

/-! ## The methods are typed at the recursor's case types -/

section MethodTyping

variable {R : Rules Head} (levels : LevelModel R L) {T : DeclName} {u v : Head}
  (hu : R.isUniverse u) (hv : R.isUniverse v)
  (typeT : ∀ {n : Nat} {Γ : Ctx Head n}, Typed R Γ (.const T) (.head u))
  {e : (i : Nat) → Tm Head i} {s d : Nat} {C : Tm Head (s + 1 + d)}
  (scrutinee : e s = .const T)
  (motiveTyped : Typed R (ofEntries e (s + 1)) (piRange e (s + 1) d C) (.head v))
include levels hu hv typeT scrutinee motiveTyped

/-- The type of motives is formed, and the motive's body is a type of `v` over
the scrutinee. -/
theorem recMotive_parts {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m}
    (mor : SubstMor R (ofEntries e s) Δ pre) :
    (∃ w, R.isUniverse w ∧ Typed R Δ (.pi (.const T) (.head v)) (.head w)) ∧
      Typed R (.snoc Δ (.const T)) (Presentation.subst (liftSub pre) (piRange e (s + 1) d C))
        (.head v) := by
  obtain ⟨v', hv', tv, _⟩ := levels.successor hv
  obtain ⟨w, join⟩ := levels.join_exists hu hv'
  refine ⟨⟨w, (levels.join_level join).1, .piForm typeT hu (.headType tv) hv' join⟩, ?_⟩
  have lifted := SubstMor.lift mor (e s)
  have h := motiveTyped.substitute lifted
  have hs : Presentation.subst pre (e s) = .const T := by
    rw [scrutinee]
    rfl
  rw [hs] at h
  exact h

/-- The motive, at the arguments `pre` before the scrutinee. -/
theorem recMotive_typed {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m}
    (mor : SubstMor R (ofEntries e s) Δ pre) :
    Typed R Δ (Presentation.subst pre (recMotive e s d C)) (.pi (.const T) (.head v)) := by
  obtain ⟨⟨w, hw, tPi⟩, body⟩ := recMotive_parts levels hu hv typeT scrutinee motiveTyped mor
  exact .lamIntro tPi hw body

/-- The motive applied to a scrutinee is the type of the function of the later
arguments. -/
theorem recMotive_beta {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m}
    (mor : SubstMor R (ofEntries e s) Δ pre) {x : Tm Head m} (hx : Typed R Δ x (.const T)) :
    TypeEq R Δ (.app (Presentation.subst pre (recMotive e s d C)) x)
      (Presentation.subst (consSub x pre) (piRange e (s + 1) d C)) := by
  obtain ⟨⟨w, hw, tPi⟩, body⟩ := recMotive_parts levels hu hv typeT scrutinee motiveTyped mor
  have h := Derivable.betaPi tPi hw body hx
  rw [inst0_subst_liftSub] at h
  exact ⟨v, hv, h⟩

variable {k : DeclName} {fields : List (Field Head)}
  {body : Tm Head (s + fields.length + d + (recPositions fields).length)}
  (ctor : ∀ {n : Nat} {Γ : Ctx Head n}, Typed R Γ (.const k) (liftClosed (ctorType T fields)))
  (bodyTyped : Typed R (hypCtx T k e s d fields C) body
    (Presentation.rename (wkN (recPositions fields).length)
      (Presentation.subst (patternSub s fields.length d k) C)))
include ctor bodyTyped

/-- The method's core: over typed fields and typed hypotheses, the later
arguments abstracted over the placed right-hand side have the motive's type at
the constructor form. -/
theorem methodCore_typed {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m}
    (mor : SubstMor R (ofEntries e s) Δ pre) {xs : List (Tm Head m)}
    (typedXs : List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fields xs)
    {hs : List (Tm Head m)}
    (typedHs : List.Forall₂
      (fun r h => Typed R Δ h (.app (Presentation.subst pre (recMotive e s d C)) r))
      (recArgs fields xs) hs) :
    Typed R Δ (methodCore s d k fields body pre xs hs)
      (.app (Presentation.subst pre (recMotive e s d C)) (appSpine (.const k) xs)) := by
  have hx : xs.length = fields.length := typedXs.length_eq.symm
  have tK : Typed R Δ (appSpine (.const k) xs) (.const T) := ctorApp_typed ctor typedXs
  have mor₀ : SubstMor R (ofEntries e (s + 1)) Δ (consSub (appSpine (.const k) xs) pre) := by
    refine SubstMor.cons mor ?_
    rw [scrutinee]
    exact tK
  have morAll : SubstMor R (ofEntries e (s + 1 + d))
      (extendEntries Δ (laterEntries e s (consSub (appSpine (.const k) xs) pre)) d)
      (liftSubN (consSub (appSpine (.const k) xs) pre) d) := by
    rw [ofEntries_add e (s + 1) d]
    exact SubstMor.liftN mor₀ (fun j => e (s + 1 + j)) d
  have hscrut : scrutOf s d (liftSubN (consSub (appSpine (.const k) xs) pre) d) =
      appSpine (.const k) (xs.map (Presentation.rename (wkN d))) := by
    rw [scrutOf_liftSubN, consSub_zero, rename_appSpine]
    rfl
  have typedXs' : ∀ l, l < fields.length →
      Typed R (extendEntries Δ (laterEntries e s (consSub (appSpine (.const k) xs) pre)) d)
        ((xs.map (Presentation.rename (wkN d))).getD l defaultTm)
        (liftClosed ((fields.getD l .recursive).type T)) := by
    intro l hl
    rw [getD_map_rename]
    have h := (forall₂_getD .recursive defaultTm typedXs l hl).rename (ctxRen_wkN Δ (laterEntries e s (consSub (appSpine (.const k) xs) pre)) d)
    rwa [rename_liftClosed] at h
  have morP := SubstMor.pattern e fields typedXs' (by rw [List.length_map, hx]) d morAll hscrut
  have typedH : ∀ j, j < (recPositions fields).length →
      Typed R (extendEntries Δ (laterEntries e s (consSub (appSpine (.const k) xs) pre)) d)
        (Presentation.rename (wkN d) (hs.getD j defaultTm))
        (Presentation.subst (matchSub s fields.length (xs.map (Presentation.rename (wkN d))) d
            (liftSubN (consSub (appSpine (.const k) xs) pre) d))
          (recCallType e s fields.length d ((recPositions fields).getD j 0) C)) := by
    intro j hj
    obtain ⟨hl, hrec⟩ := recPositions_spec fields j hj
    rw [getD_of_lt 0 hj, subst_recCallType e _ _ C hl, getD_map_rename, prefixSub_liftSubN]
    have eq : Presentation.subst
          (consSub (Presentation.rename (wkN d) (xs.getD (recPositions fields)[j] defaultTm))
            (fun i => Presentation.rename (wkN d) (tailSub (consSub (appSpine (.const k) xs) pre) i)))
          (piRange e (s + 1) d C) =
        Presentation.rename (wkN d)
          (Presentation.subst (consSub (xs.getD (recPositions fields)[j] defaultTm) pre)
            (piRange e (s + 1) d C)) := by
      rw [rename_subst]
      congr 1
      funext i
      exact Fin.cases rfl (fun i => rfl) i
    rw [eq]
    refine Typed.rename ?_ (ctxRen_wkN Δ (laterEntries e s (consSub (appSpine (.const k) xs) pre)) d)
    have hxT : Typed R Δ (xs.getD (recPositions fields)[j] defaultTm) (.const T) := by
      have h := forall₂_getD .recursive defaultTm typedXs _ hl
      rw [hrec] at h
      exact h
    have hh := forall₂_getD defaultTm defaultTm typedHs j
      (by rw [recArgs_length_eq fields xs hx]; exact hj)
    rw [recArgs_getD fields xs hx j hj, getD_of_lt 0 hj] at hh
    exact Typed.convType hh (recMotive_beta levels hu hv typeT scrutinee motiveTyped mor hxT)
  have morH := SubstMor.hyps
    (fun j => recCallType e s fields.length d ((recPositions fields).getD j 0) C) morP
    (recPositions fields).length typedH
  have bodyT := bodyTyped.substitute morH
  rw [subst_extendSub_wkN, subst_comp] at bodyT
  have pat : (fun ι => Presentation.subst
      (matchSub s fields.length (xs.map (Presentation.rename (wkN d))) d
        (liftSubN (consSub (appSpine (.const k) xs) pre) d)) (patternSub s fields.length d k ι)) =
      liftSubN (consSub (appSpine (.const k) xs) pre) d := by
    funext ι
    rw [subst_matchSub_patternSub k _ (by rw [List.length_map, hx]) d _ ι, ← hscrut,
      replaceScrut_self]
  rw [pat] at bodyT
  have formedPR := motiveTyped.substitute mor₀
  rw [piRange_eq_pis, subst_pis] at formedPR
  obtain ⟨formedEntries, formedC⟩ := IsType.pis_inv d ⟨v, hv, formedPR⟩
  obtain ⟨lamT, _⟩ := Typed.lams levels d formedEntries formedC bodyT
  refine Typed.convType lamT ?_
  have b := recMotive_beta levels hu hv typeT scrutinee motiveTyped mor tK
  rw [piRange_eq_pis, subst_pis] at b
  exact b.symm

/-- The hypotheses' abstractions: with `done` already bound as `hs`, the
remaining recursive arguments `rs` are abstracted in order. -/
theorem methodHyps_typed :
    ∀ (c : Nat) {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m},
      SubstMor R (ofEntries e s) Δ pre →
      ∀ {xs : List (Tm Head m)},
        List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) fields xs →
      ∀ {done hs rs : List (Tm Head m)}, recArgs fields xs = done ++ rs → rs.length = c →
        List.Forall₂
          (fun r h => Typed R Δ h (.app (Presentation.subst pre (recMotive e s d C)) r)) done hs →
        Typed R Δ (methodHyps s d k fields body c pre xs hs)
            (caseHyps (Presentation.subst pre (recMotive e s d C)) rs (appSpine (.const k) xs)) ∧
          IsType R Δ
            (caseHyps (Presentation.subst pre (recMotive e s d C)) rs (appSpine (.const k) xs))
  | 0, m, Δ, pre, mor, xs, typedXs, done, hs, rs, split, hc, typedHs => by
      obtain rfl : rs = [] := List.length_eq_zero_iff.mp hc
      rw [List.append_nil] at split
      rw [← split] at typedHs
      rw [caseHyps_nil]
      have tK := ctorApp_typed ctor typedXs
      refine ⟨methodCore_typed levels hu hv typeT scrutinee motiveTyped ctor bodyTyped mor
        typedXs typedHs, v, hv, ?_⟩
      exact Derivable.appElim (recMotive_typed levels hu hv typeT scrutinee motiveTyped mor) tK
  | c + 1, m, Δ, pre, mor, xs, typedXs, done, hs, rs, split, hc, typedHs => by
      obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
        cases rs with
        | nil => exact absurd hc.symm (Nat.succ_ne_zero _)
        | cons r rs' => exact ⟨r, rs', rfl⟩
      have tP := recMotive_typed levels hu hv typeT scrutinee motiveTyped mor
      have tr : Typed R Δ r (.const T) :=
        recArgs_typed typedXs r (by rw [split]; exact List.mem_append_right _ (List.mem_cons_self ..))
      have tpr : Typed R Δ (.app (Presentation.subst pre (recMotive e s d C)) r) (.head v) :=
        Derivable.appElim tP tr
      have hp₁ : Presentation.rename wk (Presentation.subst pre (recMotive e s d C)) =
          Presentation.subst (wkSub pre) (recMotive e s d C) := rename_subst _ _ _
      have mor₁ := SubstMor.wk mor (.app (Presentation.subst pre (recMotive e s d C)) r)
      have typedXs₁ := forall₂_fields_weaken
        (A := .app (Presentation.subst pre (recMotive e s d C)) r) typedXs
      have split₁ : recArgs fields (xs.map (Presentation.rename wk)) =
          (done.map (Presentation.rename wk) ++ [Presentation.rename wk r]) ++
            rs'.map (Presentation.rename wk) := by
        rw [← rename_recArgs, split, List.map_append, List.map_cons, List.append_assoc]
        rfl
      have typedHs₁ : List.Forall₂
          (fun r' h => Typed R (.snoc Δ (.app (Presentation.subst pre (recMotive e s d C)) r))
            h (.app (Presentation.subst (wkSub pre) (recMotive e s d C)) r'))
          (done.map (Presentation.rename wk) ++ [Presentation.rename wk r])
          (hs.map (Presentation.rename wk) ++ [.var 0]) := by
        refine List.rel_append ?_ (.cons ?_ .nil)
        · have h := forall₂_hyps_weaken
            (A := .app (Presentation.subst pre (recMotive e s d C)) r) typedHs
          rwa [hp₁] at h
        · have h := Derivable.var (R := R)
            (Γ := .snoc Δ (.app (Presentation.subst pre (recMotive e s d C)) r)) 0
          rw [Ctx.lookup_snoc_zero] at h
          show Typed R _ (.var 0)
            (.app (Presentation.subst (wkSub pre) (recMotive e s d C)) (Presentation.rename wk r))
          rw [← hp₁]
          exact h
      obtain ⟨ih, w₁, hw₁, tRest⟩ := methodHyps_typed c mor₁ typedXs₁ split₁
        (by rw [List.length_map]; exact Nat.succ.inj hc) typedHs₁
      obtain ⟨w, join⟩ := levels.join_exists hv hw₁
      have hw := (levels.join_level join).1
      have e₁ : Presentation.rename wk (appSpine (.const k) xs) =
          appSpine (.const k) (xs.map (Presentation.rename wk)) := rename_appSpine _ _ _
      rw [caseHyps_cons, e₁, hp₁]
      have tPi : Typed R Δ (.pi (.app (Presentation.subst pre (recMotive e s d C)) r)
          (caseHyps (Presentation.subst (wkSub pre) (recMotive e s d C))
            (rs'.map (Presentation.rename wk)) (appSpine (.const k) (xs.map (Presentation.rename wk)))))
          (.head w) := .piForm tpr hv tRest hw₁ join
      exact ⟨.lamIntro tPi hw ih, w, hw, tPi⟩

/-- The fields' abstractions: with `done` already bound as `xs`, the remaining
fields `fs` are abstracted in order. -/
theorem methodFields_typed
    (fieldTyped : ∀ {F : Tm Head 0}, Field.closed F ∈ fields → Typed R .nil F (.head u)) :
    ∀ (fs : List (Field Head)) {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m},
      SubstMor R (ofEntries e s) Δ pre →
      ∀ {done : List (Field Head)} {xs recs : List (Tm Head m)}, fields = done ++ fs →
        List.Forall₂ (fun f x => Typed R Δ x (liftClosed (Field.type T f))) done xs →
        recs = recArgs done xs →
        Typed R Δ (methodFields s d k fields body fs pre xs)
            (caseFields T k fs (Presentation.subst pre (recMotive e s d C)) xs recs) ∧
          IsType R Δ (caseFields T k fs (Presentation.subst pre (recMotive e s d C)) xs recs)
  | [], m, Δ, pre, mor, done, xs, recs, hf, typedXs, hrecs => by
      rw [List.append_nil] at hf
      subst hf
      have hx : xs.length = fields.length := typedXs.length_eq.symm
      show Typed R Δ (methodHyps s d k fields body (recPositions fields).length pre xs [])
          (caseHyps _ recs _) ∧ IsType R Δ (caseHyps _ recs _)
      exact methodHyps_typed levels hu hv typeT scrutinee motiveTyped ctor bodyTyped
        (recPositions fields).length mor typedXs (done := []) (by rw [hrecs]; rfl)
        (by rw [hrecs, recArgs_length_eq fields xs hx]) .nil
  | f :: fs, m, Δ, pre, mor, done, xs, recs, hf, typedXs, hrecs => by
      have hx : xs.length = done.length := typedXs.length_eq.symm
      have hp₁ : Presentation.rename wk (Presentation.subst pre (recMotive e s d C)) =
          Presentation.subst (wkSub pre) (recMotive e s d C) := rename_subst _ _ _
      have hf₁ : fields = (done ++ [f]) ++ fs := by rw [hf, List.append_assoc]; rfl
      have formedF : IsType R Δ (liftClosed (Field.type T f)) := by
        cases f with
        | recursive => exact ⟨u, hu, typeT⟩
        | closed F =>
            have mem : Field.closed F ∈ fields := by
              rw [hf]; exact List.mem_append_right _ (List.mem_cons_self ..)
            exact ⟨u, hu, Typed.liftClosed (fieldTyped mem)⟩
      have mor₁ := SubstMor.wk mor (liftClosed (Field.type T f))
      have typedXs₁ : List.Forall₂
          (fun g x => Typed R (.snoc Δ (liftClosed (Field.type T f))) x (liftClosed (Field.type T g)))
          (done ++ [f]) (xs.map (Presentation.rename wk) ++ [.var 0]) := by
        refine List.rel_append (forall₂_fields_weaken typedXs) (.cons ?_ .nil)
        have h := Derivable.var (R := R) (Γ := .snoc Δ (liftClosed (Field.type T f))) 0
        rw [Ctx.lookup_snoc_zero, rename_liftClosed] at h
        exact h
      have recs₁ : recArgs (done ++ [f]) (xs.map (Presentation.rename wk) ++ [.var 0]) =
          recs.map (Presentation.rename wk) ++ recArgs [f] [.var 0] := by
        rw [recArgs_snoc done _ f _ (by rw [List.length_map, hx]), hrecs, rename_recArgs]
      obtain ⟨ih, w₁, hw₁, tRest⟩ := methodFields_typed fieldTyped fs mor₁ hf₁ typedXs₁ recs₁.symm
      obtain ⟨uF, huF, tF⟩ := formedF
      obtain ⟨w, join⟩ := levels.join_exists huF hw₁
      have hw := (levels.join_level join).1
      cases f with
      | recursive =>
          have tPi : Typed R Δ (.pi (.const T) (caseFields T k fs
              (Presentation.rename wk (Presentation.subst pre (recMotive e s d C)))
              (xs.map (Presentation.rename wk) ++ [.var 0])
              (recs.map (Presentation.rename wk) ++ [.var 0]))) (.head w) := by
            rw [hp₁]
            exact .piForm tF huF tRest hw₁ join
          have ih' : Typed R (.snoc Δ (.const T))
              (methodFields s d k fields body fs (wkSub pre) (xs.map (Presentation.rename wk) ++ [.var 0]))
              (caseFields T k fs (Presentation.rename wk (Presentation.subst pre (recMotive e s d C)))
                (xs.map (Presentation.rename wk) ++ [.var 0])
                (recs.map (Presentation.rename wk) ++ [.var 0])) := by
            rw [hp₁]
            exact ih
          exact ⟨.lamIntro tPi hw ih', w, hw, tPi⟩
      | closed F =>
          have e0 : recs.map (Presentation.rename wk) ++
              recArgs [Field.closed F] [(.var 0 : Tm Head (m + 1))] = recs.map (Presentation.rename wk) :=
            List.append_nil _
          rw [e0] at ih tRest
          have tPi : Typed R Δ (.pi (liftClosed F) (caseFields T k fs
              (Presentation.rename wk (Presentation.subst pre (recMotive e s d C)))
              (xs.map (Presentation.rename wk) ++ [.var 0])
              (recs.map (Presentation.rename wk)))) (.head w) := by
            rw [hp₁]
            exact .piForm tF huF tRest hw₁ join
          have ih' : Typed R (.snoc Δ (liftClosed F))
              (methodFields s d k fields body fs (wkSub pre) (xs.map (Presentation.rename wk) ++ [.var 0]))
              (caseFields T k fs (Presentation.rename wk (Presentation.subst pre (recMotive e s d C)))
                (xs.map (Presentation.rename wk) ++ [.var 0])
                (recs.map (Presentation.rename wk))) := by
            rw [hp₁]
            exact ih
          exact ⟨.lamIntro tPi hw ih', w, hw, tPi⟩

/-- The method of a constructor, at typed arguments before the scrutinee, has
the recursor's case type over the motive. -/
theorem method_typed
    (fieldTyped : ∀ {F : Tm Head 0}, Field.closed F ∈ fields → Typed R .nil F (.head u))
    {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m} (mor : SubstMor R (ofEntries e s) Δ pre) :
    Typed R Δ (methodFields s d k fields body fields pre [])
      (caseType T k fields (Presentation.subst pre (recMotive e s d C))) :=
  (methodFields_typed levels hu hv typeT scrutinee motiveTyped ctor bodyTyped fieldTyped fields mor
    (done := []) (xs := []) (recs := []) (List.nil_append _).symm .nil rfl).1

end MethodTyping

/-! ## The recursor applied to the motive and the methods -/

/-- The motive and the methods of a structural recursion at the arguments
`pre` before the scrutinee, in constructor order: the recursor's arguments
before the scrutinee. -/
def recPre (e : (i : Nat) → Tm Head i) (s d : Nat) (C : Tm Head (s + 1 + d))
    (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    {m : Nat} (pre : Sub Head s m) : List (Tm Head m) :=
  Presentation.subst pre (recMotive e s d C) ::
    ctors.map (fun c => methodFields s d c.1 c.2 (body c.1 c.2) c.2 pre [])

theorem subst_recPre (e : (i : Nat) → Tm Head i) (s d : Nat) (C : Tm Head (s + 1 + d))
    (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    {n m : Nat} (τ : Sub Head n m) (pre : Sub Head s n) :
    (recPre e s d C ctors body pre).map (Presentation.subst τ) =
      recPre e s d C ctors body (fun i => Presentation.subst τ (pre i)) := by
  unfold recPre
  rw [List.map_cons, List.map_map, subst_comp]
  congr 1
  apply List.map_congr_left
  intro c _
  show Presentation.subst τ (methodFields s d c.1 c.2 (body c.1 c.2) c.2 pre []) = _
  rw [subst_methodFields]
  rfl

/-- The recursive call of the recursor-built function on the field at position
`l`, in the context of an equation: the recursor at the variables before the
scrutinee, applied to the field's variable. -/
def recCallRec (rec : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat) (C : Tm Head (s + 1 + d))
    (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    (a l : Nat) : Tm Head (s + a + d) :=
  recApp rec (recPre e s d C ctors body (tailSub (callSub s a d l))) (callSub s a d l 0)

/-- The substitution of the hypotheses by the recursive calls of the
recursor-built function. -/
def recHypSub (rec : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat) (C : Tm Head (s + 1 + d))
    (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    (fields : List (Field Head)) :
    Sub Head (s + fields.length + d + (recPositions fields).length) (s + fields.length + d) :=
  extendSub ids
    (fun j => recCallRec rec e s d C ctors body fields.length ((recPositions fields).getD j 0))
    (recPositions fields).length

theorem subst_recCallRec (rec : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (C : Tm Head (s + 1 + d)) (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    {m a : Nat} (as : List (Tm Head m)) (σ : Sub Head (s + 1 + d) m) {l : Nat} (hl : l < a) :
    Presentation.subst (matchSub s a as d σ) (recCallRec rec e s d C ctors body a l) =
      recApp rec (recPre e s d C ctors body (prefixSub s d σ)) (as.getD l defaultTm) := by
  unfold recCallRec
  rw [subst_recApp, subst_recPre]
  have h := callSub_matchSub as d σ l hl
  have tail : (fun i => Presentation.subst (matchSub s a as d σ) (tailSub (callSub s a d l) i)) =
      prefixSub s d σ := by
    funext i
    exact congrFun h i.succ
  rw [tail]
  exact congrArg _ (congrFun h 0)

section RecursorTyping

variable {R : Rules Head}

/-- A typed substitution of the recursor's prefix from a typed motive and typed
methods. -/
theorem substMor_recPrefix {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))}
    {m : Nat} {Δ : Ctx Head m} {P : Tm Head m} {ms : List (Tm Head m)}
    (tP : Typed R Δ P (.pi (.const T) (.head v)))
    (tms : List.Forall₂ (fun c mt => Typed R Δ mt (caseType T c.1 c.2 P)) ctors ms) :
    ∀ (j : Nat), j ≤ ctors.length →
      SubstMor R (ofEntries (recEntry T v ctors) (j + 1)) Δ (argsSub (j + 1) (P :: ms.take j))
  | 0, _ => by
      have e : (P :: ms.take 0) = [] ++ [P] := rfl
      rw [e, argsSub_concat (N := 0) (l := []) P rfl]
      exact SubstMor.cons (fun i => Fin.elim0 i) tP
  | j + 1, hj => by
      have hlen : ms.length = ctors.length := tms.length_eq.symm
      have hjm : j < ms.length := by omega
      have e : (P :: ms.take (j + 1)) = (P :: ms.take j) ++ [ms[j]] := by
        rw [List.take_succ_eq_append_getElem hjm]
        rfl
      rw [e, argsSub_concat _ (by rw [List.length_cons, List.length_take]; omega)]
      refine SubstMor.cons (substMor_recPrefix tP tms j (by omega)) ?_
      have hget : ctors[j]? = some ctors[j] := List.getElem?_eq_getElem (by omega)
      obtain ⟨b, hb, tb⟩ := forall₂_getElem? tms hget
      rw [List.getElem?_eq_getElem hjm] at hb
      obtain rfl := Option.some.inj hb
      rcases hc : ctors[j] with ⟨k, fields⟩
      rw [hc] at hget tb
      rw [recEntry_method T v ctors hget, subst_caseType]
      have hlast : argsSub (j + 1) (P :: ms.take j) (Fin.last j) = P := by
        show (P :: ms.take j).getD (j + 1 - 1 - j) (.const .anonymous) = P
        rw [show j + 1 - 1 - j = 0 by omega]
        rfl
      show Typed R Δ ms[j] (caseType T k fields (argsSub (j + 1) (P :: ms.take j) (Fin.last j)))
      rw [hlast]
      exact tb

/-- The recursor applied to a typed motive, typed methods and a scrutinee. -/
theorem recApp_typed {T rec : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))}
    (recTyping : ∀ {n : Nat} {Γ : Ctx Head n},
      Typed R Γ (.const rec) (liftClosed (recType T v ctors)))
    {m : Nat} {Δ : Ctx Head m} {P : Tm Head m} {ms : List (Tm Head m)}
    (tP : Typed R Δ P (.pi (.const T) (.head v)))
    (tms : List.Forall₂ (fun c mt => Typed R Δ mt (caseType T c.1 c.2 P)) ctors ms)
    {t : Tm Head m} (ht : Typed R Δ t (.const T)) :
    Typed R Δ (recApp rec (P :: ms) t) (.app P t) := by
  have hlen : ms.length = ctors.length := tms.length_eq.symm
  have pre := substMor_recPrefix tP tms ctors.length (Nat.le_refl _)
  rw [List.take_of_length_le (by omega)] at pre
  have hl : ((P :: ms) ++ [t]).length = ctors.length + 1 + 1 := by
    rw [List.length_append, List.length_cons, hlen]
    rfl
  have mor : SubstMor R (ofEntries (recEntry T v ctors) (ctors.length + 1 + 1)) Δ
      (argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t])) := by
    rw [argsSub_concat t (by rw [List.length_cons, hlen])]
    refine SubstMor.cons pre ?_
    rw [recEntry_scrutinee]
    exact ht
  have h := Typed.telescope_apply (Θ := ofEntries (recEntry T v ctors) (ctors.length + 1 + 1))
    (X := recBody ctors.length) mor recTyping
  rw [applyClosed_eq_appSpine, telescopeArgs_argsSub _ _ _ hl] at h
  have body : Presentation.subst (argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t]))
      (recBody ctors.length) = .app P t := by
    show Tm.app (argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t]) (Fin.last (ctors.length + 1)))
      (argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t]) 0) = _
    have first : argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t]) (Fin.last (ctors.length + 1)) = P := by
      show ((P :: ms) ++ [t]).getD (ctors.length + 1 + 1 - 1 - (ctors.length + 1)) _ = P
      rw [show ctors.length + 1 + 1 - 1 - (ctors.length + 1) = 0 by omega]
      rfl
    have second : argsSub (ctors.length + 1 + 1) ((P :: ms) ++ [t]) 0 = t := by
      show ((P :: ms) ++ [t]).getD (ctors.length + 1 + 1 - 1 - 0) _ = t
      rw [List.getD_eq_getElem?_getD,
        show ctors.length + 1 + 1 - 1 - 0 = (P :: ms).length by rw [List.length_cons, hlen]; omega,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    rw [first, second]
  rw [body] at h
  exact h

end RecursorTyping

/-- A function typed at the recursion's type of the later arguments, at the
arguments before them, applied to the later arguments. -/
theorem Typed.suffix_apply {R : Rules Head} {e : (i : Nat) → Tm Head i} {s : Nat} :
    ∀ (d : Nat) {C : Tm Head (s + 1 + d)} {m : Nat} {Δ : Ctx Head m} {σ : Sub Head (s + 1 + d) m},
      SubstMor R (ofEntries e (s + 1 + d)) Δ σ →
      ∀ {g : Tm Head m},
        Typed R Δ g (Presentation.subst (consSub (scrutOf s d σ) (prefixSub s d σ))
          (piRange e (s + 1) d C)) →
        Typed R Δ (appSpine g (suffixArgs s d σ)) (Presentation.subst σ C)
  | 0, C, m, Δ, σ, _, g, tg => by
      have e0 : consSub (scrutOf s 0 σ) (prefixSub s 0 σ) = σ := consSub_tailSub σ
      rw [e0] at tg
      exact tg
  | d + 1, C, m, Δ, σ, mor, g, tg => by
      have ih := Typed.suffix_apply d (C := .pi (e (s + 1 + d)) C) (SubstMor.tail mor) (g := g) tg
      have app := Derivable.appElim ih (SubstMor.head mor)
      rw [inst0_subst_liftSub, consSub_tailSub] at app
      show Typed R Δ (appSpine g (suffixArgs s d (tailSub σ) ++ [σ 0])) (Presentation.subst σ C)
      rw [appSpine_concat]
      exact app

/-- The arguments of the telescope are recovered from their prefix, scrutinee
and suffix: the suffix substituted for the later variables of the lifted
prefix and scrutinee. -/
theorem recompose_args {m s : Nat} :
    ∀ (d : Nat) (σ : Sub Head (s + 1 + d) m),
      (fun i => Presentation.subst (extendSub ids (fun j => (suffixArgs s d σ).getD j defaultTm) d)
        (liftSubN (consSub (scrutOf s d σ) (prefixSub s d σ)) d i)) = σ
  | 0, σ => by
      funext i
      show Presentation.subst ids (consSub (σ 0) (tailSub σ) i) = σ i
      rw [subst_ids, consSub_tailSub]
  | d + 1, σ => by
      funext i
      have hlen := suffixArgs_length (s := s) d (tailSub σ)
      have values : extendSub ids (fun j => (suffixArgs s (d + 1) σ).getD j defaultTm) (d + 1) =
          consSub (σ 0) (extendSub ids (fun j => (suffixArgs s d (tailSub σ)).getD j defaultTm) d) := by
        show consSub ((suffixArgs s d (tailSub σ) ++ [σ 0]).getD d defaultTm)
          (extendSub ids (fun j => (suffixArgs s d (tailSub σ) ++ [σ 0]).getD j defaultTm) d) = _
        have last : (suffixArgs s d (tailSub σ) ++ [σ 0]).getD d defaultTm = σ 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          rfl
        have same : extendSub ids (fun j => (suffixArgs s d (tailSub σ) ++ [σ 0]).getD j defaultTm) d =
            extendSub ids (fun j => (suffixArgs s d (tailSub σ)).getD j defaultTm) d :=
          extendSub_congr ids d (fun j hj => by
            show (suffixArgs s d (tailSub σ) ++ [σ 0]).getD j defaultTm =
              (suffixArgs s d (tailSub σ)).getD j defaultTm
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_append_left (by omega)])
        rw [last, same]
      rw [values]
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · show Presentation.subst _ (Presentation.rename wk
          (liftSubN (consSub (scrutOf s d (tailSub σ)) (prefixSub s d (tailSub σ))) d i)) = σ i.succ
        rw [subst_consSub_rename_wk]
        exact congrFun (recompose_args d (tailSub σ)) i

/-- The right-hand side with the recursor's recursive calls, under the match:
each hypothesis becomes the recursor applied at the matched field. -/
theorem subst_recHypSub (rec : DeclName) (e : (i : Nat) → Tm Head i) (s d : Nat)
    (C : Tm Head (s + 1 + d)) (ctors : List (DeclName × List (Field Head)))
    (body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length))
    {m : Nat} (fields : List (Field Head)) (as : List (Tm Head m)) (σ : Sub Head (s + 1 + d) m)
    (b : Tm Head (s + fields.length + d + (recPositions fields).length)) :
    Presentation.subst (matchSub s fields.length as d σ)
        (Presentation.subst (recHypSub rec e s d C ctors body fields) b) =
      Presentation.subst (extendSub (matchSub s fields.length as d σ)
        (fun j => recApp rec (recPre e s d C ctors body (prefixSub s d σ))
          (as.getD ((recPositions fields).getD j 0) defaultTm))
        (recPositions fields).length) b := by
  rw [subst_comp]
  congr 1
  unfold recHypSub
  rw [subst_extendSub]
  apply extendSub_congr
  intro j hj
  obtain ⟨hl, _⟩ := recPositions_spec fields j hj
  rw [getD_of_lt 0 hj]
  exact subst_recCallRec rec e s d C ctors body as σ hl

theorem Reduces.appSpine_left {R : Rules Head} {n : Nat} {g g' : Tm Head n}
    (red : Reduces R g g') (args : List (Tm Head n)) :
    Reduces R (appSpine g args) (appSpine g' args) :=
  Reduces.congr (f := fun x => appSpine x args) (fun st => stepCore_appSpine args st) red

/-! ## The recursion's equations hold for the recursor -/

section Derivation

variable {S : Setting Head L} {R₀ R₁ R₂ : Rules Head} {T : DeclName} {u : Head}
  {ctors : List (DeclName × List (Field Head))} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S R₀ R₁ R₂ T u ctors rec v)
  {e : (i : Nat) → Tm Head i} {s d : Nat} {C : Tm Head (s + 1 + d)}
  {body : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (s + fields.length + d + (recPositions fields).length)}
  (scrutinee : e s = .const T)
  (motiveTyped : Typed S.R (ofEntries e (s + 1)) (piRange e (s + 1) d C) (.head v))
  (bodyTyped : ∀ {k : DeclName} {fields : List (Field Head)}, (k, fields) ∈ ctors →
    Typed S.R (hypCtx T k e s d fields C) (body k fields)
      (Presentation.rename (wkN (recPositions fields).length)
        (Presentation.subst (patternSub s fields.length d k) C)))
include ind scrutinee motiveTyped bodyTyped

/-- The recursor applied to the motive and the methods at typed arguments
before the scrutinee, and to a scrutinee of the inductive type, has the
recursion's type of the later arguments there. -/
theorem DeclaresInductive.recursor_typed {m : Nat} {Δ : Ctx Head m} {pre : Sub Head s m}
    (mor : SubstMor S.R (ofEntries e s) Δ pre) {t : Tm Head m} (ht : Typed S.R Δ t (.const T)) :
    Typed S.R Δ (recApp rec (recPre e s d C ctors body pre) t)
      (Presentation.subst (consSub t pre) (piRange e (s + 1) d C)) := by
  have typeT : ∀ {n : Nat} {Γ : Ctx Head n}, Typed S.R Γ (.const T) (.head u) := ind.typing
  have tP := recMotive_typed S.levels ind.hu ind.hv typeT scrutinee motiveTyped mor
  have tms : List.Forall₂
      (fun c mt => Typed S.R Δ mt (caseType T c.1 c.2 (Presentation.subst pre (recMotive e s d C))))
      ctors (ctors.map (fun c => methodFields s d c.1 c.2 (body c.1 c.2) c.2 pre [])) :=
    forall₂_map_self _ ctors (fun c hc =>
      method_typed S.levels ind.hu ind.hv typeT scrutinee motiveTyped (ind.ctor_typing hc)
        (bodyTyped hc) (fun hF => Derivable.mono ind.sub₀ (ind.fieldTyped hc hF)) mor)
  exact Typed.convType (recApp_typed ind.toRecursor.rec_typing tP tms ht)
    (recMotive_beta S.levels ind.hu ind.hv typeT scrutinee motiveTyped mor ht)

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
include facts roots heads

/-- **The recursion's equations are derivable for the recursor.** At every typed
argument substitution whose scrutinee is a constructor form, the recursor
applied to the motive and the methods built from the right-hand sides, then to
the later arguments, equals the constructor's right-hand side with each
recursive hypothesis replaced by the recursor's own recursive call. The proof
is one ι-step followed by β-steps. -/
theorem DeclaresInductive.recursor_equation {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ)
    {σ : Sub Head (s + 1 + d) n} (mor : SubstMor S.R (ofEntries e (s + 1 + d)) Δ σ)
    {i : Nat} {k : DeclName} {fields : List (Field Head)} (hi : ctors[i]? = some (k, fields))
    {as : List (Tm Head n)} (has : as.length = fields.length)
    (hscrut : scrutOf s d σ = appSpine (.const k) as) :
    Equal S.R Δ
      (appSpine (recApp rec (recPre e s d C ctors body (prefixSub s d σ)) (scrutOf s d σ))
        (suffixArgs s d σ))
      (Presentation.subst (matchSub s fields.length as d σ)
        (Presentation.subst (recHypSub rec e s d C ctors body fields) (body k fields)))
      (Presentation.subst σ C) := by
  have morPre := SubstMor.prefixSub e d mor
  have tScrut : Typed S.R Δ (scrutOf s d σ) (.const T) := by
    have h := SubstMor.scrut e d mor
    rw [scrutinee] at h
    exact h
  have lhsTyped := Typed.suffix_apply d mor
    (ind.recursor_typed scrutinee motiveTyped bodyTyped morPre tScrut)
  refine (Reduces.preserve facts roots heads formed ?_ lhsTyped).2
  rw [hscrut]
  have hms : (ctors.map (fun c => methodFields s d c.1 c.2 (body c.1 c.2) c.2 (prefixSub s d σ) [])).length =
      ctors.length := List.length_map ..
  have hm : (ctors.map (fun c => methodFields s d c.1 c.2 (body c.1 c.2) c.2 (prefixSub s d σ) []))[i]? =
      some (methodFields s d k fields (body k fields) fields (prefixSub s d σ) []) := by
    rw [List.getElem?_map, hi]
    rfl
  have iota := ind.iota (p := Presentation.subst (prefixSub s d σ) (recMotive e s d C)) hms hi has hm
  refine (Reduces.appSpine_step (.root iota) (suffixArgs s d σ)).trans ?_
  have hlen : ((recArgs fields as).map
      (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))).length =
        (recPositions fields).length := by
    rw [List.length_map, recArgs_length_eq fields as has]
  have h1 := Reduces.appSpine_left (R := S.R) (Reduces.appSpine_left (R := S.R)
    (methodFields_beta (R := S.R) s d k fields (body k fields) fields (prefixSub s d σ) [] as has)
    ((recArgs fields as).map (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))))
    (suffixArgs s d σ)
  rw [List.nil_append] at h1
  have h2 := Reduces.appSpine_left (R := S.R)
    (methodHyps_beta (R := S.R) s d k fields (body k fields) (recPositions fields).length
      (prefixSub s d σ) as [] _ hlen) (suffixArgs s d σ)
  rw [List.nil_append] at h2
  have h3 := lams_beta (R := S.R) d
    (Presentation.subst (placeSub s d k fields (prefixSub s d σ) as
      ((recArgs fields as).map (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))))
      (body k fields))
    (suffixArgs s d σ) (suffixArgs_length d σ)
  rw [appSpine_append]
  refine h1.trans (h2.trans (h3.trans (Reduces.of_eq ?_)))
  -- The reduct is the right-hand side.
  have lhs : (fun ι => Presentation.subst
        (extendSub ids (fun j => (suffixArgs s d σ).getD j defaultTm) d)
        (placeSub s d k fields (prefixSub s d σ) as
          ((recArgs fields as).map (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))) ι)) =
      extendSub (matchSub s fields.length as d σ)
        (fun j => ((recArgs fields as).map
          (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))).getD j defaultTm)
        (recPositions fields).length := by
    unfold placeSub
    rw [subst_extendSub_comp, subst_matchSub]
    have asEq : (as.map (Presentation.rename (wkN d))).map
        (Presentation.subst (extendSub ids (fun j => (suffixArgs s d σ).getD j defaultTm) d)) = as := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id as]
      exact List.map_congr_left (fun x _ => by
        show Presentation.subst _ (Presentation.rename (wkN d) x) = x
        rw [subst_extendSub_wkN, subst_ids])
    have argsEq : (fun i => Presentation.subst
        (extendSub ids (fun j => (suffixArgs s d σ).getD j defaultTm) d)
        (formArgs s d k (prefixSub s d σ) as i)) = σ := by
      unfold formArgs
      rw [← hscrut]
      exact recompose_args d σ
    rw [asEq, argsEq]
    congr 1
    funext j
    rw [subst_extendSub_wkN, subst_ids]
  have rhs : (fun ι => Presentation.subst (matchSub s fields.length as d σ)
        (recHypSub rec e s d C ctors body fields ι)) =
      extendSub (matchSub s fields.length as d σ)
        (fun j => recApp rec (recPre e s d C ctors body (prefixSub s d σ))
          (as.getD ((recPositions fields).getD j 0) defaultTm))
        (recPositions fields).length := by
    unfold recHypSub
    rw [subst_extendSub]
    apply extendSub_congr
    intro j hj
    obtain ⟨hl, _⟩ := recPositions_spec fields j hj
    rw [getD_of_lt 0 hj]
    exact subst_recCallRec rec e s d C ctors body as σ hl
  have calls : ∀ j, j < (recPositions fields).length →
      ((recArgs fields as).map (recApp rec (recPre e s d C ctors body (prefixSub s d σ)))).getD j
          defaultTm =
        recApp rec (recPre e s d C ctors body (prefixSub s d σ))
          (as.getD ((recPositions fields).getD j 0) defaultTm) := by
    intro j hj
    have hjr : j < (recArgs fields as).length := by
      rw [recArgs_length_eq fields as has]
      exact hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjr]
    show recApp rec _ (recArgs fields as)[j] = _
    rw [← recArgs_getD fields as has j hj, getD_of_lt defaultTm hjr]
  rw [subst_comp, subst_comp, lhs, rhs, extendSub_congr _ _ calls]

/-- The derived equation with the right-hand side computed: each recursive
hypothesis is the recursor applied at the matched field. -/
theorem DeclaresInductive.recursor_equation_matched {n : Nat} {Δ : Ctx Head n}
    (formed : CtxFormed S.R Δ)
    {σ : Sub Head (s + 1 + d) n} (mor : SubstMor S.R (ofEntries e (s + 1 + d)) Δ σ)
    {i : Nat} {k : DeclName} {fields : List (Field Head)} (hi : ctors[i]? = some (k, fields))
    {as : List (Tm Head n)} (has : as.length = fields.length)
    (hscrut : scrutOf s d σ = appSpine (.const k) as) :
    Equal S.R Δ
      (appSpine (recApp rec (recPre e s d C ctors body (prefixSub s d σ)) (scrutOf s d σ))
        (suffixArgs s d σ))
      (Presentation.subst (extendSub (matchSub s fields.length as d σ)
        (fun j => recApp rec (recPre e s d C ctors body (prefixSub s d σ))
          (as.getD ((recPositions fields).getD j 0) defaultTm))
        (recPositions fields).length) (body k fields))
      (Presentation.subst σ C) := by
  have h := ind.recursor_equation scrutinee motiveTyped bodyTyped facts roots heads formed
    mor hi has hscrut
  rwa [subst_recHypSub] at h

end Derivation

/-- **A definition by structural recursion is derivable from the recursor.** The
recursor applied to the motive and to the methods built from the definition's
own right-hand sides satisfies each of the definition's equations, the
definition's recursive calls becoming the recursor's. The one side condition
is that the recursor eliminates into a universe holding the recursion's
result family. -/
theorem DeclaresRecursion.recursor_derivable {S : Setting Head L} {R₀ : Rules Head} {f T : DeclName}
    {ctors : List (DeclName × List (Field Head))} {e : (i : Nat) → Tm Head i} {s d : Nat}
    {C : Tm Head (s + 1 + d)}
    {body : (k : DeclName) → (fields : List (Field Head)) →
      Tm Head (s + fields.length + d + (recPositions fields).length)}
    (decl : DeclaresRecursion S R₀ f T ctors e s d C body)
    {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
    (ind : DeclaresInductive S R₀' R₁' R₂' T u ctors rec v)
    (motiveTyped : Typed S.R (ofEntries e (s + 1)) (piRange e (s + 1) d C) (.head v))
    (facts : FormFacts S.R S.roles)
    (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
    {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ)
    {σ : Sub Head (s + 1 + d) n} (mor : SubstMor S.R (ofEntries e (s + 1 + d)) Δ σ)
    {i : Nat} {k : DeclName} {fields : List (Field Head)} (hi : ctors[i]? = some (k, fields))
    {as : List (Tm Head n)} (has : as.length = fields.length)
    (hscrut : scrutOf s d σ = appSpine (.const k) as) :
    Equal S.R Δ
      (appSpine (recApp rec (recPre e s d C ctors body (prefixSub s d σ)) (scrutOf s d σ))
        (suffixArgs s d σ))
      (Presentation.subst (matchSub s fields.length as d σ)
        (Presentation.subst (recHypSub rec e s d C ctors body fields) (body k fields)))
      (Presentation.subst σ C) :=
  ind.recursor_equation decl.scrutinee motiveTyped
    (fun mem => Derivable.mono decl.sub₀ (decl.bodyTyped mem)) facts roots heads formed
    mor hi has hscrut

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
