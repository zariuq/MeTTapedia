import Mettapedia.OSLF.Syntax.Strengthening

/-!
# Recognition of injective typed variable arguments

This recognizes the explicit arguments of a contextual metavariable. It does
not infer a declaration or an ambient-depth permission. The result packages
the selected renaming, its existing `Strengthener`, and its actual reading by
`argsToSub`. Repeated variables are outside this injective profile, not
necessarily outside the set of solvable instantiation problems.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

def prependRen {Γ Δ : Ctx S} {a : S.Srt} (head : Var Δ a) (tail : Ren S Γ Δ) :
    Ren S (a :: Γ) Δ
  | _, .zero => head
  | s, .succ v => tail s v

variable [DecidableEq S.Srt]

def prependInverse {Γ Δ : Ctx S} {a : S.Srt} (head : Var Δ a)
    {tail : Ren S Γ Δ} (St : Strengthener tail) (s : S.Srt) (v : Var Δ s) :
    Option (Var (a :: Γ) s) :=
  if hs : s = a then
    if hs ▸ v = head then some (hs.symm ▸ Var.zero) else (St.un s v).map Var.succ
  else (St.un s v).map Var.succ

def Strengthener.prepend {Γ Δ : Ctx S} {a : S.Srt} (head : Var Δ a)
    {tail : Ren S Γ Δ} (St : Strengthener tail) (fresh : St.un a head = none) :
    Strengthener (prependRen head tail) where
  un := prependInverse head St
  un_rho := by
    intro s v
    cases v with
    | zero => simp [prependInverse, prependRen]
    | succ v =>
        by_cases hs : s = a
        · subst s
          have distinct : tail a v ≠ head := by
            intro equality
            have found := St.un_rho a v
            rw [equality, fresh] at found
            cases found
          simp [prependInverse, prependRen, distinct, St.un_rho]
        · simp [prependInverse, prependRen, hs, St.un_rho]
  rho_un := by
    intro s v w found
    by_cases hs : s = a
    · subst s
      by_cases hv : v = head
      · subst v
        simp [prependInverse] at found
        cases found
        rfl
      · simp [prependInverse, hv, Option.map_eq_some_iff] at found
        obtain ⟨inner, hi, rfl⟩ := found
        exact St.rho_un _ _ _ hi
    · simp only [prependInverse, dif_neg hs, Option.map_eq_some_iff] at found
      obtain ⟨inner, hi, rfl⟩ := found
      exact St.rho_un _ _ _ hi

/-- An operational recognition result, not a new assignment representation. -/
structure VariableArguments {dependencies ambient : Ctx S}
    (args : Args S (dependencies.map (fun s => ([], s))) ambient) where
  rho : Ren S dependencies ambient
  inverse : Strengthener rho
  realizes : ∀ s v, argsToSub args s v = Term.var (rho s v)

def recognizeVariableArguments : {dependencies ambient : Ctx S} →
    (args : Args S (dependencies.map (fun s => ([], s))) ambient) →
    Option (VariableArguments args)
  | [], _, .nil => some
      { rho := fun _ v => nomatch v
        inverse :=
          { un := fun _ _ => none
            un_rho := fun _ v => nomatch v
            rho_un := by intro s v w; exact nomatch w }
        realizes := fun _ v => nomatch v }
  | _ :: _, _, .cons (.op _ _) _ => none
  | a :: _, _, .cons (.var head) tail =>
      match recognizeVariableArguments tail with
      | none => none
      | some selected =>
          if fresh : selected.inverse.un a head = none then
            some
              { rho := prependRen head selected.rho
                inverse := selected.inverse.prepend head fresh
                realizes := by
                  intro s v
                  cases v with
                  | zero => rfl
                  | succ v => exact selected.realizes s v }
          else none

omit [DecidableEq S.Srt] in
theorem VariableArguments.injective {dependencies ambient : Ctx S}
    {args : Args S (dependencies.map (fun s => ([], s))) ambient}
    (selected : VariableArguments args) (s : S.Srt) :
    Function.Injective (selected.rho s) := by
  intro v w equality
  have hv := selected.inverse.un_rho s v
  have hw := selected.inverse.un_rho s w
  rw [equality, hw] at hv
  exact (Option.some.inj hv).symm

omit [DecidableEq S.Srt] in
/-- The recognized spine applies a body by the existing renaming action. -/
theorem VariableArguments.bind_eq_rename {dependencies ambient : Ctx S}
    {args : Args S (dependencies.map (fun s => ([], s))) ambient}
    (selected : VariableArguments args) {s : S.Srt} (body : Term S dependencies s) :
    bind (argsToSub args) body = rename selected.rho body := by
  have realization : argsToSub args = fun s v => Term.var (selected.rho s v) :=
    funext fun s => funext fun v => selected.realizes s v
  rw [realization, bind_var_eq_rename]

/-- Every explicitly supplied injective variable spine is recognized. -/
theorem recognizeVariableArguments_complete : ∀ {dependencies ambient : Ctx S}
    (args : Args S (dependencies.map (fun s => ([], s))) ambient)
    (rho : Ren S dependencies ambient),
    (∀ s v, argsToSub args s v = Term.var (rho s v)) →
    (∀ s, Function.Injective (rho s)) →
    ∃ selected, recognizeVariableArguments args = some selected
  | [], _, .nil, _, _, _ => ⟨_, rfl⟩
  | a :: dependencies, ambient, .cons head tail, rho, realizes, injective => by
      cases head with
      | op o args =>
          have impossible := realizes a Var.zero
          cases impossible
      | var head =>
          let tailRho : Ren S dependencies ambient := fun s v => rho s (.succ v)
          have tailRealizes : ∀ s v, argsToSub tail s v = Term.var (tailRho s v) :=
            fun s v => realizes s (.succ v)
          have tailInjective : ∀ s, Function.Injective (tailRho s) := by
            intro s v w equality
            have same := injective s equality
            exact Var.succ.inj same
          obtain ⟨selected, recognized⟩ :=
            recognizeVariableArguments_complete tail tailRho tailRealizes tailInjective
          have sameHead : rho a Var.zero = head :=
            (Term.var.inj (realizes a Var.zero)).symm
          have sameTail : ∀ s v, selected.rho s v = rho s (.succ v) := by
            intro s v
            exact Term.var.inj ((selected.realizes s v).symm.trans (tailRealizes s v))
          have fresh : selected.inverse.un a head = none := by
            cases found : selected.inverse.un a head with
            | none => rfl
            | some v =>
                have hit := selected.inverse.rho_un a head v found
                rw [sameTail, ← sameHead] at hit
                have impossible := injective a hit
                cases impossible
          simp only [recognizeVariableArguments, recognized, dif_pos fresh]
          exact ⟨_, rfl⟩

/-- This is precisely an injective variable profile, not general solvability. -/
theorem recognizeVariableArguments_success_iff {dependencies ambient : Ctx S}
    (args : Args S (dependencies.map (fun s => ([], s))) ambient) :
    (∃ selected, recognizeVariableArguments args = some selected) ↔
      ∃ rho : Ren S dependencies ambient,
        (∀ s v, argsToSub args s v = Term.var (rho s v)) ∧
        (∀ s, Function.Injective (rho s)) := by
  constructor
  · rintro ⟨selected, _⟩
    exact ⟨selected.rho, selected.realizes, selected.injective⟩
  · rintro ⟨rho, realizes, injective⟩
    exact recognizeVariableArguments_complete args rho realizes injective

theorem recognizeVariableArguments_none_iff {dependencies ambient : Ctx S}
    (args : Args S (dependencies.map (fun s => ([], s))) ambient) :
    recognizeVariableArguments args = none ↔
      ¬ ∃ rho : Ren S dependencies ambient,
        (∀ s v, argsToSub args s v = Term.var (rho s v)) ∧
        (∀ s, Function.Injective (rho s)) := by
  rw [← recognizeVariableArguments_success_iff]
  cases recognizeVariableArguments args <;> simp

end Mettapedia.OSLF.Binding
