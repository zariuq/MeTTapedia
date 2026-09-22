import Mettapedia.GSLT.LanguageDef.VariableArgumentInstantiation

/-!
# Bound-prefix projection of contextual arguments

The original strengthening traversal projects away the ordinary rule-variable
context. The partial inverse is derived from `splitVar`, not from a capture
depth. Recovery below is deliberately restricted to bound-variable arguments;
rejecting an ordinary argument is not a claim of general unsolvability.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}

theorem splitVar_recombine {Γ : Ctx S} :
    ∀ (bs : Ctx S) {s : S.Srt} (v : Var (bs ++ Γ) s),
      Sum.elim (injPrefix bs) (weakenVar bs) (splitVar bs v) = v
  | [], _, _ => rfl
  | _ :: rest, _, .zero => rfl
  | _ :: rest, _, .succ v => by
      have ih := splitVar_recombine rest v
      cases found : splitVar rest v with
      | inl w =>
          simp only [found, Sum.elim_inl] at ih
          simpa only [splitVar, found, Sum.elim_inl, injPrefix] using congrArg Var.succ ih
      | inr w =>
          simp only [found, Sum.elim_inr] at ih
          simpa only [splitVar, found, Sum.elim_inr, weakenVar] using congrArg Var.succ ih

/-- The existing prefix injection has a partial inverse that rejects Γ. -/
def Strengthener.boundPrefix (bs Γ : Ctx S) :
    Strengthener (fun _ v => injPrefix (Γ := Γ) bs v) where
  un := fun _ v => match splitVar bs v with
    | .inl w => some w
    | .inr _ => none
  un_rho := by intro s v; simp only [splitVar_injPrefix]
  rho_un := by
    intro s v w found
    have reconstructed := splitVar_recombine bs v
    cases split : splitVar bs v with
    | inl u =>
        simp only [split] at found
        cases found
        simpa only [split, Sum.elim_inl] using reconstructed
    | inr u => simp only [split] at found; cases found

theorem strengthenA_boundPrefix_iff {bs Γ : Ctx S}
    {arity : List (List S.Srt × S.Srt)} (args : Args S arity (bs ++ Γ))
    (projected : Args S arity bs) :
    strengthenA (Strengthener.boundPrefix bs Γ) args = some projected ↔
      renameArgs (fun _ v => injPrefix (Γ := Γ) bs v) projected = args := by
  constructor
  · exact renameArgs_strengthenA _ args projected
  · intro equality
    rw [← equality, strengthenA_renameArgs]

theorem strengthenA_boundPrefix_none_iff {bs Γ : Ctx S}
    {arity : List (List S.Srt × S.Srt)} (args : Args S arity (bs ++ Γ)) :
    strengthenA (Strengthener.boundPrefix bs Γ) args = none ↔
      ¬ ∃ projected, renameArgs (fun _ v => injPrefix (Γ := Γ) bs v) projected = args := by
  constructor
  · intro rejected ⟨projected, equality⟩
    have hit := (strengthenA_boundPrefix_iff args projected).mpr equality
    rw [rejected] at hit
    cases hit
  · intro absent
    cases found : strengthenA (Strengthener.boundPrefix bs Γ) args with
    | none => rfl
    | some projected => exact False.elim (absent ⟨projected,
        (strengthenA_boundPrefix_iff args projected).mp found⟩)

variable {M : List (MetaArity S)}

theorem injPrefix_withMetas {Γ : Ctx S} : ∀ (bs : Ctx S) {s : S.Srt} (v : Var bs s),
    injPrefix (S := withMetas S M) (Γ := Γ) bs v = injPrefix (S := S) bs v
  | [], _, v => nomatch v
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ v => congrArg Var.succ (injPrefix_withMetas rest v)

/-- Actual metasubstitution commutes with this checked projection. -/
theorem projected_arguments_instantiate {dependencies bs Γ : Ctx S}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (projected : Args (withMetas S M) (dependencies.map (fun s => ([], s))) bs)
    (found : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args = some projected)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    {s : S.Srt} (body : Term S dependencies s) :
    bind (argsToSub (instantiateArgs assignment args)) body =
      rename (fun _ v => injPrefix (Γ := Γ) bs v)
        (bind (argsToSub (instantiateArgs assignment projected)) body) := by
  have equality := (strengthenA_boundPrefix_iff args projected).mp found
  rw [← equality, instantiateArgs_renameArgs, rename_bind]
  simp only [injPrefix_withMetas]
  congr 1
  funext sort v
  exact argsToSub_renameArgs (fun _ v => injPrefix (Γ := Γ) bs v)
    dependencies (instantiateArgs assignment projected) sort v

/-- Closing ordinary rule variables preserves a body recovered from the bound
prefix, using exactly the existing slot-scoping operation. -/
theorem projected_recovery_reads_slot [DecidableEq S.Srt]
    {dependencies bs Γ : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (projected : Args (withMetas S M) (dependencies.map (fun s => ([], s))) bs)
    (found : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args = some projected)
    (selected : VariableArguments projected)
    (recognized : recognizeVariableArguments projected = some selected)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (target : Term S (bs ++ []) s) (body : Term S dependencies s)
    (recovered : recoverVariableArgumentBody projected (unScope bs target) = some body)
    (sigma : Sub S Γ []) :
    bind (liftSub sigma bs) (bind (argsToSub (instantiateArgs assignment args)) body) =
      target := by
  rw [projected_arguments_instantiate args projected found assignment body,
    (recoverVariableArgumentBody_eq_some_iff projected selected recognized assignment
      (unScope bs target) body).mp recovered]
  exact bind_reads_slot_back sigma bs target

/-- The original whole-prefix spine is exactly the injected identity spine. -/
theorem prefixArgs_eq_injected_idArgs (bs Γ : Ctx S) :
    prefixArgs (T := withMetas S M) (Γ := Γ) bs =
      renameArgs (fun _ v => injPrefix (S := withMetas S M) (Γ := Γ) bs v)
        (idArgs (S := S) (M := M) bs) := by
  have realizes : argsToSub (prefixArgs (T := withMetas S M) (Γ := Γ) bs) =
      fun s v => Term.var (S := withMetas S M)
        (injPrefix (S := withMetas S M) (Γ := Γ) bs v) :=
    funext fun s => funext fun v => argsToSub_prefixArgs (T := withMetas S M) bs s v
  calc
    _ = bindArgs (argsToSub (prefixArgs (T := withMetas S M) (Γ := Γ) bs))
        (idArgs bs) := (bindArgs_argsToSub_idArgs bs _).symm
    _ = _ := by rw [realizes, bindArgs_var_eq_renameArgs]

theorem strengthenA_prefixArgs (bs Γ : Ctx S) :
    strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ)
      (prefixArgs (T := withMetas S M) (Γ := Γ) bs) = some (idArgs bs) := by
  rw [prefixArgs_eq_injected_idArgs, strengthenA_renameArgs]

theorem recognizeVariableArguments_idArgs [DecidableEq S.Srt] (bs : Ctx S) :
    ∃ selected, recognizeVariableArguments (idArgs (S := S) (M := M) bs) = some selected := by
  apply recognizeVariableArguments_complete _ (fun _ v => v)
  · exact argsToSub_idArgs bs
  · intro s v w equality; exact equality

/-- Recovery at the old full-prefix profile returns precisely its old body. -/
theorem recoverVariableArgumentBody_idArgs [DecidableEq S.Srt]
    {bs : Ctx S} {s : S.Srt} (target : Term S bs s) :
    recoverVariableArgumentBody (idArgs (S := S) (M := M) bs) target = some target := by
  obtain ⟨selected, found⟩ := recognizeVariableArguments_idArgs (S := S) (M := M) bs
  have rho_id : selected.rho = fun _ v => v := by
    funext sort v
    exact Term.var.inj (S := withMetas S M)
      ((selected.realizes sort v).symm.trans (argsToSub_idArgs bs sort v))
  rw [recoverVariableArgumentBody, found]
  have roundtrip := strengthenT_rename selected.baseInverse target
  simpa only [rho_id, rename_id] using roundtrip

theorem unScopeVar_injPrefix : ∀ (bs : Ctx S) {s : S.Srt} (v : Var bs s),
    unScopeVar bs (injPrefix (Γ := []) bs v) = v
  | [], _, v => nomatch v
  | _ :: _, _, .zero => rfl
  | _ :: rest, _, .succ v => congrArg Var.succ (unScopeVar_injPrefix rest v)

theorem unScope_rename_injPrefix {bs : Ctx S} {s : S.Srt} (term : Term S bs s) :
    unScope bs (rename (fun _ v => injPrefix (Γ := []) bs v) term) = term := by
  simp only [unScope, rename_comp, unScopeVar_injPrefix, rename_id]

/-- Reading back a prefix term is independent of the ordinary closing substitution. -/
theorem unScope_bind_injPrefix {bs Γ : Ctx S} {s : S.Srt}
    (sigma : Sub S Γ []) (term : Term S bs s) :
    unScope bs (bind (liftSub sigma bs)
      (rename (fun _ v => injPrefix (Γ := Γ) bs v) term)) = term := by
  have reconstructed := bind_reads_slot_back sigma bs
    (rename (fun _ v => injPrefix (Γ := []) bs v) term)
  rw [unScope_rename_injPrefix] at reconstructed
  rw [reconstructed, unScope_rename_injPrefix]

end Mettapedia.OSLF.Binding
