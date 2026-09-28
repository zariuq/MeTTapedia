import Mettapedia.OSLF.Syntax.BoundPrefixProjection

/-!
# Scoped schema matching

The existing schema matcher and accumulator live above strengthening so typed
contextual argument recovery can reuse the shared scope operations.

One mutual algorithm tracks an accumulated bound prefix. Rigid operators
recurse through their slots; ordinary rule variables retain closed assignments,
and contextual metavariables use their supplied injective bound-variable spines.
This is a supported matching profile, not general higher-order unification:
repeated or nonvariable arguments can be declined even when instantiation exists.
-/

namespace Mettapedia.OSLF.Binding

set_option autoImplicit false

variable {S : Signature}
variable [opDec : ∀ s : S.Srt, DecidableEq (S.Op s)]
variable [DecidableEq S.Srt] {M : List (MetaArity S)}

omit opDec in
/-- Compose the existing bound-prefix projection, variable recognition, and
body strengthening. Ordinary rule variables are not bound dependencies. -/
def recoverBoundVariableBody {dependencies bs Γ : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (target : Term S (bs ++ []) s) : Option (Term S dependencies s) :=
  match strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args with
  | none => none
  | some projected => recoverVariableArgumentBody projected (unScope bs target)

omit opDec in
theorem recoverBoundVariableBody_sound {dependencies bs Γ : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (target : Term S (bs ++ []) s) (result : Term S dependencies s)
    (found : recoverBoundVariableBody args target = some result)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (sigma : Sub S Γ []) :
    bind (liftSub sigma bs) (bind (argsToSub (instantiateArgs assignment args)) result) =
      target := by
  unfold recoverBoundVariableBody at found
  cases projected : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args with
  | none => simp only [projected] at found; cases found
  | some spine =>
      simp only [projected] at found
      cases recognized : recognizeVariableArguments spine with
      | none => simp only [recoverVariableArgumentBody, recognized] at found; cases found
      | some selected =>
          exact projected_recovery_reads_slot args spine projected selected recognized
            assignment target result found sigma

omit opDec in
theorem recoverBoundVariableBody_prefix {bs Γ : Ctx S} {s : S.Srt}
    (target : Term S (bs ++ []) s) :
    recoverBoundVariableBody (prefixArgs (T := withMetas S M) (Γ := Γ) bs) target =
      some (unScope bs target) := by
  simp only [recoverBoundVariableBody, strengthenA_prefixArgs, recoverVariableArgumentBody_idArgs]

omit opDec in
/-- On the recognized injective bound-variable profile, recovery is exactly
actual instantiated application followed by ordinary-variable closing. -/
theorem recoverBoundVariableBody_eq_some_iff {dependencies bs Γ : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (projected : Args (withMetas S M) (dependencies.map (fun s => ([], s))) bs)
    (projection : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args =
      some projected)
    (selected : VariableArguments projected)
    (recognized : recognizeVariableArguments projected = some selected)
    (target : Term S (bs ++ []) s) (result : Term S dependencies s)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (sigma : Sub S Γ []) :
    recoverBoundVariableBody args target = some result ↔
      bind (liftSub sigma bs) (bind (argsToSub (instantiateArgs assignment args)) result) =
        target := by
  constructor
  · intro found
    exact recoverBoundVariableBody_sound args target result found assignment sigma
  · intro equality
    have readBack := congrArg (unScope bs) equality
    rw [projected_arguments_instantiate args projected projection assignment result,
      unScope_bind_injPrefix] at readBack
    simp only [recoverBoundVariableBody, projection]
    exact (recoverVariableArgumentBody_eq_some_iff projected selected recognized assignment
      (unScope bs target) result).mpr readBack

omit opDec in
theorem recoverBoundVariableBody_eq_none_iff {dependencies bs Γ : Ctx S} {s : S.Srt}
    (args : Args (withMetas S M) (dependencies.map (fun s => ([], s))) (bs ++ Γ))
    (projected : Args (withMetas S M) (dependencies.map (fun s => ([], s))) bs)
    (projection : strengthenA (Strengthener.boundPrefix (S := withMetas S M) bs Γ) args =
      some projected)
    (selected : VariableArguments projected)
    (recognized : recognizeVariableArguments projected = some selected)
    (target : Term S (bs ++ []) s)
    (assignment : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (sigma : Sub S Γ []) :
    recoverBoundVariableBody args target = none ↔
      ¬ ∃ result, bind (liftSub sigma bs)
        (bind (argsToSub (instantiateArgs assignment args)) result) = target := by
  constructor
  · intro absent ⟨result, equality⟩
    have found := (recoverBoundVariableBody_eq_some_iff args projected projection selected
      recognized target result assignment sigma).mpr equality
    rw [absent] at found
    cases found
  · intro absent
    cases found : recoverBoundVariableBody args target with
    | none => rfl
    | some result => exact False.elim (absent ⟨result,
        (recoverBoundVariableBody_eq_some_iff args projected projection selected recognized
          target result assignment sigma).mp found⟩)

omit opDec in
/-- Every previously accepted whole-prefix check returns the same body,
including its original dependent context cast. -/
theorem recoverBoundVariableBody_old_prefix {Γ : Ctx S}
    (bs ar : Ctx S) (hb : ar = bs) {s : S.Srt}
    (target : Term S (bs ++ []) s)
    (args : Args (withMetas S M) (ar.map (fun s => ([], s))) (bs ++ Γ))
    (accepted : varArgsEq (castArgsArity (T := withMetas S M)
      (congrArg (List.map (fun s => ([], s))) hb) args)
      (prefixArgs (T := withMetas S M) (Γ := Γ) bs) = true) :
    recoverBoundVariableBody args target = some (castTermCtx hb.symm (unScope bs target)) := by
  subst hb
  have equality := varArgsEq_sound _ _ accepted
  simp only [castArgsArity] at equality
  rw [equality]
  exact recoverBoundVariableBody_prefix target

/-- What matching a schema has found: closed terms for the rule's own
variables, and bodies for its metavariables. -/
structure MAcc (S : Signature) (M : List (MetaArity S)) (Γ : Ctx S) where
  vars : PSub S Γ
  metas : (i : Fin M.length) → Option (Term S (M.get i).1 (M.get i).2)

/-- Nothing found yet. -/
def emptyMAcc {Γ : Ctx S} : MAcc S M Γ := ⟨emptyPSub, fun _ => none⟩

/-- Record one metavariable's body. -/
def setMeta {Γ : Ctx S} (acc : MAcc S M Γ) (i : Fin M.length)
    (t : Term S (M.get i).1 (M.get i).2) : MAcc S M Γ :=
  { acc with metas := fun j => if h : i = j then some (h ▸ t) else acc.metas j }


mutual
/-- Match beneath an accumulated bound prefix; Γ continues to hold only
ordinary variables whose assignments are closed. -/
def smatchAtT : {Γ : Ctx S} → (β : Ctx S) → {s : S.Srt} →
    MAcc S M Γ → Term (withMetas S M) (β ++ Γ) s → Term S (β ++ []) s →
    Option (MAcc S M Γ)
  | _, β, _, acc, .var x, target =>
      match splitVar β x with
      | .inl v => if target = .var (injPrefix (Γ := []) β v) then some acc else none
      | .inr y =>
          match strengthenT (Strengthener.ofWeakenPrefix S (Γ := []) β) target with
          | none => none
          | some closed =>
              match acc.vars _ y with
              | none => some { acc with vars := updatePSub acc.vars y closed }
              | some old => if old = closed then some acc else none
  | _, β, _, acc, .op (.inr (.mk i)) args, target =>
      match recoverBoundVariableBody args target with
      | none => none
      | some recovered =>
          match acc.metas i with
          | none => some (setMeta acc i recovered)
          | some old => if old = recovered then some acc else none
  | _, β, _, acc, .op (.inl f) args, .op f' args' =>
      if same : f = f' then by
        subst same
        exact smatchAtA β acc args args'
      else none
  | _, _, _, _, .op (.inl _) _, .var _ => none
termination_by _ _ _ _ pattern _ => 2 * termSize pattern
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- Each argument prepends its own binders to the accumulated prefix. -/
def smatchAtA : {Γ : Ctx S} → (β : Ctx S) →
    {arity : List (List S.Srt × S.Srt)} → MAcc S M Γ →
    Args (withMetas S M) arity (β ++ Γ) → Args S arity (β ++ []) →
    Option (MAcc S M Γ)
  | _, _, _, acc, .nil, .nil => some acc
  | Γ, β, _, acc, .cons (bs := bs) head tail, .cons target targetTail =>
      match smatchAtT (bs ++ β) acc
        (castTermCtx (T := withMetas S M) (List.append_assoc bs β Γ).symm head)
        (castTermCtx (T := S) (List.append_assoc bs β []).symm target) with
      | none => none
      | some next => smatchAtA β next tail targetTail
termination_by _ _ _ _ pattern _ => 2 * argsSize pattern + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

/-- Closed-target endpoint of the single prefix-indexed matcher. -/
def smatchT {Γ : Ctx S} {s : S.Srt} (acc : MAcc S M Γ)
    (pattern : Term (withMetas S M) Γ s) (target : Term S [] s) : Option (MAcc S M Γ) :=
  smatchAtT [] acc pattern target

/-- Argument endpoint of the single prefix-indexed matcher. -/
def smatchA {Γ : Ctx S} {arity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (pattern : Args (withMetas S M) arity Γ)
    (target : Args S arity []) : Option (MAcc S M Γ) :=
  smatchAtA [] acc pattern target

@[simp] theorem smatchAtA_nil {Γ : Ctx S} (β : Ctx S) (acc : MAcc S M Γ) :
    smatchAtA β acc .nil .nil = some acc := by rw [smatchAtA]

/-- One accumulator says everything another does. -/
def MAccLe {Γ : Ctx S} (acc acc' : MAcc S M Γ) : Prop :=
  (∀ (r : S.Srt) (y : Var Γ r) (u : Term S [] r),
      acc.vars r y = some u → acc'.vars r y = some u)
  ∧ (∀ (i : Fin M.length) (u : Term S (M.get i).1 (M.get i).2),
      acc.metas i = some u → acc'.metas i = some u)

omit opDec [DecidableEq S.Srt] in
theorem MAccLe.refl {Γ : Ctx S} (acc : MAcc S M Γ) : MAccLe acc acc :=
  ⟨fun _ _ _ h => h, fun _ _ h => h⟩

omit opDec [DecidableEq S.Srt] in
theorem MAccLe.trans {Γ : Ctx S} {a b c : MAcc S M Γ}
    (h₁ : MAccLe a b) (h₂ : MAccLe b c) : MAccLe a c :=
  ⟨fun r y u h => h₂.1 r y u (h₁.1 r y u h), fun i u h => h₂.2 i u (h₁.2 i u h)⟩

omit opDec [DecidableEq S.Srt] in
/-- Recording a metavariable that was not yet recorded adds only it. -/
theorem MAccLe.setMeta {Γ : Ctx S} (acc : MAcc S M Γ) (i : Fin M.length)
    (t : Term S (M.get i).1 (M.get i).2) (hi : acc.metas i = none) :
    MAccLe acc (setMeta acc i t) := by
  refine ⟨fun _ _ _ h => h, ?_⟩
  intro j u hj
  simp only [_root_.Mettapedia.OSLF.Binding.setMeta]
  by_cases hij : i = j
  · subst hij; rw [hi] at hj; exact absurd hj (by simp)
  · simp [hij, hj]

omit opDec in
/-- Recording a variable that was not yet recorded adds only it. -/
theorem MAccLe.setVar {Γ : Ctx S} {c : S.Srt} (acc : MAcc S M Γ) (x : Var Γ c)
    (t : Term S [] c) (hx : acc.vars c x = none) :
    MAccLe acc { acc with vars := updatePSub acc.vars x t } := by
  refine ⟨?_, fun _ _ h => h⟩
  intro r y u h
  exact updatePSub_mono acc.vars x t hx r y u h


omit opDec [DecidableEq S.Srt] in
/-- **The slot case, with its arity equality taken over a variable.**  Stating
it this way is what lets the equality be eliminated: neither side of the
matcher's own check is a variable, so the casts there cannot be discharged in
place, but they can be here, and the matcher instantiates this at its own
arity. -/
theorem slot_sound_aux {Γ : Ctx S} (sigma : Sub S Γ [])
    (bs ar : List S.Srt) (hb : ar = bs) {s : S.Srt}
    (tgt : Term S (bs ++ []) s)
    (margs : Args (withMetas S M) (ar.map (fun c => ([], c))) (bs ++ Γ))
    (hargs : castArgsArity (T := withMetas S M)
        (congrArg (List.map (fun c => ([], c))) hb) margs
        = prefixArgs (T := withMetas S M) (Γ := Γ) bs)
    (bi : Term S ar s) (hbi : bi = castTermCtx hb.symm (unScope bs tgt))
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    bind (liftSub sigma bs) (bind (argsToSub (instantiateArgs body margs)) bi) = tgt := by
  subst hb
  simp only [castArgsArity, castTermCtx] at hargs hbi
  subst hargs
  subst hbi
  have hsub : argsToSub (instantiateArgs body (prefixArgs (T := withMetas S M) ar))
      = fun r y => Term.var (S := S) (injPrefix (Γ := Γ) ar y) := by
    rw [instantiateArgs_prefixArgs]
    funext r y
    exact argsToSub_prefixArgs (T := S) ar r y
  rw [hsub]
  exact bind_prefix_slot sigma ar tgt

omit opDec [DecidableEq S.Srt] in
/-- Recording a metavariable records it. -/
theorem setMeta_self {Γ : Ctx S} (acc : MAcc S M Γ) (i : Fin M.length)
    (t : Term S (M.get i).1 (M.get i).2) : (setMeta acc i t).metas i = some t := by
  simp [setMeta]

/-- A closing substitution and a body assignment realise an accumulator when
they agree with everything it has recorded. -/
def MExtends {Γ : Ctx S} (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (acc : MAcc S M Γ) : Prop :=
  (∀ (r : S.Srt) (y : Var Γ r) (u : Term S [] r), acc.vars r y = some u → sigma r y = u)
  ∧ (∀ (i : Fin M.length) (u : Term S (M.get i).1 (M.get i).2),
      acc.metas i = some u → body i = u)

omit opDec [DecidableEq S.Srt] in
/-- Realising a later accumulator realises an earlier one. -/
theorem MExtends.mono {Γ : Ctx S} {sigma : Sub S Γ []} {body} {acc acc' : MAcc S M Γ}
    (hle : MAccLe acc acc') (he : MExtends sigma body acc') : MExtends sigma body acc :=
  ⟨fun r y u h => he.1 r y u (hle.1 r y u h), fun i u h => he.2 i u (hle.2 i u h)⟩


mutual
/-- Matching under any accumulated prefix only adds assignments. -/
theorem smatchAtT_mono : ∀ {Γ : Ctx S} (β : Ctx S) {s : S.Srt}
    (acc acc' : MAcc S M Γ) (p : Term (withMetas S M) (β ++ Γ) s)
    (t : Term S (β ++ []) s),
    smatchAtT β acc p t = some acc' → MAccLe acc acc'
  | _, β, _, acc, acc', .var x, t, hm => by
      rw [smatchAtT] at hm
      split at hm
      · split at hm
        · injection hm with hm; subst hm; exact MAccLe.refl acc
        · cases hm
      · next y splitEq =>
          split at hm
          · cases hm
          · next closed recovered =>
              split at hm
              · next fresh =>
                  injection hm with hm; subst hm
                  exact MAccLe.setVar acc y closed fresh
              · split at hm
                · injection hm with hm; subst hm; exact MAccLe.refl acc
                · cases hm
  | _, β, _, acc, acc', .op (.inr (.mk i)) args, t, hm => by
      rw [smatchAtT] at hm
      split at hm
      · cases hm
      · next recovered found =>
          split at hm
          · next fresh =>
              injection hm with hm; subst hm
              exact MAccLe.setMeta acc i recovered fresh
          · split at hm
            · injection hm with hm; subst hm; exact MAccLe.refl acc
            · cases hm
  | _, β, _, acc, acc', .op (.inl f) args, .op f' args', hm => by
      rw [smatchAtT] at hm
      split at hm
      · next same =>
          subst same
          exact smatchAtA_mono β acc acc' args args' hm
      · cases hm
  | _, β, _, acc, acc', .op (.inl f) args, .var v, hm => by
      rw [smatchAtT] at hm
      cases hm
termination_by _ _ _ _ _ p _ _ => 2 * termSize p
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

theorem smatchAtA_mono : ∀ {Γ : Ctx S} (β : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (acc acc' : MAcc S M Γ)
    (p : Args (withMetas S M) arity (β ++ Γ)) (t : Args S arity (β ++ [])),
    smatchAtA β acc p t = some acc' → MAccLe acc acc'
  | _, β, _, acc, acc', .nil, .nil, hm => by
      rw [smatchAtA] at hm
      injection hm with hm; subst hm; exact MAccLe.refl acc
  | Γ, β, _, acc, acc', .cons (bs := bs) head tail, .cons target targetTail, hm => by
      rw [smatchAtA] at hm
      split at hm
      · cases hm
      · next next headMatch =>
          exact MAccLe.trans (smatchAtT_mono (bs ++ β) acc next _ _ headMatch)
            (smatchAtA_mono β next acc' tail targetTail hm)
termination_by _ _ _ _ _ p _ _ => 2 * argsSize p + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

theorem smatchT_mono {Γ : Ctx S} {s : S.Srt} (acc acc' : MAcc S M Γ)
    (p : Term (withMetas S M) Γ s) (t : Term S [] s)
    (found : smatchT acc p t = some acc') : MAccLe acc acc' :=
  smatchAtT_mono [] acc acc' p t found

theorem smatchA_mono {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (acc acc' : MAcc S M Γ) (p : Args (withMetas S M) arity Γ) (t : Args S arity [])
    (found : smatchA acc p t = some acc') : MAccLe acc acc' :=
  smatchAtA_mono [] acc acc' p t found

mutual
/-- Every successful recursive match realizes actual contextual instantiation. -/
theorem smatchAtT_sound : ∀ {Γ : Ctx S} (β : Ctx S) {s : S.Srt}
    (acc acc' : MAcc S M Γ) (p : Term (withMetas S M) (β ++ Γ) s)
    (t : Term S (β ++ []) s), smatchAtT β acc p t = some acc' →
    ∀ (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2),
      MExtends sigma body acc' → bind (liftSub sigma β) (instantiate body p) = t
  | _, β, _, acc, acc', .var x, t, hm, sigma, body, he => by
      rw [smatchAtT] at hm
      split at hm
      · next v splitEq =>
          split at hm
          · next equal =>
              have rebuild := splitVar_recombine β x
              rw [splitEq] at rebuild
              simp only [Sum.elim_inl] at rebuild
              simp only [instantiate, bind]
              rw [← rebuild, liftSub_injPrefix, equal]
          · cases hm
      · next y splitEq =>
          have rebuild := splitVar_recombine β x
          rw [splitEq] at rebuild
          simp only [Sum.elim_inr] at rebuild
          split at hm
          · cases hm
          · next closed recovered =>
              have targetEq := rename_strengthenT
                (Strengthener.ofWeakenPrefix S (Γ := []) β) t closed recovered
              have assigned : sigma _ y = closed := by
                split at hm
                · injection hm with hm; subst hm
                  exact he.1 _ y closed (updatePSub_self acc.vars y closed)
                · next old stored =>
                    split at hm
                    · next equal =>
                        injection hm with hm; subst hm
                        exact (he.1 _ y old stored).trans equal
                    · cases hm
              simp only [instantiate, bind]
              rw [← rebuild, liftSub_weakenVar, assigned]
              exact targetEq
  | _, β, _, acc, acc', .op (.inr (.mk i)) args, target, hm, sigma, body, he => by
      rw [smatchAtT] at hm
      split at hm
      · cases hm
      · next recovered found =>
          have assigned : body i = recovered := by
            split at hm
            · injection hm with hm; subst hm
              exact he.2 i recovered (setMeta_self acc i recovered)
            · next old stored =>
                split at hm
                · next equal =>
                    injection hm with hm; subst hm
                    exact (he.2 i old stored).trans equal
                · cases hm
          simp only [instantiate]
          rw [assigned]
          exact recoverBoundVariableBody_sound args target recovered found body sigma
  | _, β, _, acc, acc', .op (.inl f) args, .op f' args', hm, sigma, body, he => by
      rw [smatchAtT] at hm
      split at hm
      · next same =>
          subst same
          simp only [instantiate, bind,
            smatchAtA_sound β acc acc' args args' hm sigma body he]
      · cases hm
  | _, β, _, acc, acc', .op (.inl f) args, .var v, hm, sigma, body, he => by
      rw [smatchAtT] at hm
      cases hm
termination_by _ _ _ _ _ p _ _ _ _ _ => 2 * termSize p
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

theorem smatchAtA_sound : ∀ {Γ : Ctx S} (β : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (acc acc' : MAcc S M Γ)
    (p : Args (withMetas S M) arity (β ++ Γ)) (t : Args S arity (β ++ [])),
    smatchAtA β acc p t = some acc' →
    ∀ (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2),
      MExtends sigma body acc' → bindArgs (liftSub sigma β) (instantiateArgs body p) = t
  | _, _, _, _, _, .nil, .nil, _, _, _, _ => rfl
  | Γ, β, _, acc, acc', .cons (bs := bs) head tail, .cons target targetTail,
      hm, sigma, body, he => by
      rw [smatchAtA] at hm
      split at hm
      · cases hm
      · next next headMatch =>
          have previous : MExtends sigma body next :=
            MExtends.mono (smatchAtA_mono β next acc' tail targetTail hm) he
          have headSound := smatchAtT_sound (bs ++ β) acc next _ _ headMatch sigma body previous
          rw [instantiate_castTermCtx, bind_liftSub_append] at headSound
          have uncast := castTermCtx_injective (S := S)
            (List.append_assoc bs β []).symm headSound
          simp only [instantiateArgs, bindArgs, uncast,
            smatchAtA_sound β next acc' tail targetTail hm sigma body he]
termination_by _ _ _ _ _ p _ _ _ _ _ => 2 * argsSize p + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

theorem smatchT_sound {Γ : Ctx S} {s : S.Srt} (acc acc' : MAcc S M Γ)
    (p : Term (withMetas S M) Γ s) (t : Term S [] s)
    (found : smatchT acc p t = some acc') (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (he : MExtends sigma body acc') : bind sigma (instantiate body p) = t :=
  smatchAtT_sound [] acc acc' p t found sigma body he

theorem smatchA_sound {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (acc acc' : MAcc S M Γ) (p : Args (withMetas S M) arity Γ) (t : Args S arity [])
    (found : smatchA acc p t = some acc') (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (he : MExtends sigma body acc') : bindArgs sigma (instantiateArgs body p) = t :=
  smatchAtA_sound [] acc acc' p t found sigma body he

theorem smatchAtT_castPrefix {Γ β β' : Ctx S} {s : S.Srt}
    (h : β = β') (acc : MAcc S M Γ)
    (pattern : Term (withMetas S M) (β ++ Γ) s) (target : Term S (β ++ []) s) :
    smatchAtT β' acc
      (castTermCtx (T := withMetas S M) (congrArg (fun ctx => ctx ++ Γ) h) pattern)
      (castTermCtx (T := S) (congrArg (fun ctx => ctx ++ []) h) target) =
        smatchAtT β acc pattern target := by
  cases h
  rfl

theorem smatchA_cons {Γ bs : Ctx S} {s : S.Srt}
    {arity : List (List S.Srt × S.Srt)} (acc : MAcc S M Γ)
    (head : Term (withMetas S M) (bs ++ Γ) s) (tail : Args (withMetas S M) arity Γ)
    (target : Term S (bs ++ []) s) (targetTail : Args S arity []) :
    smatchA acc (.cons head tail) (.cons target targetTail) =
      match smatchAtT bs acc head target with
      | none => none
      | some next => smatchA next tail targetTail := by
  unfold smatchA
  rw [smatchAtA]
  rw [smatchAtT_castPrefix (List.append_nil bs).symm acc head target]

/-- A supported slot keeps the original accumulator update protocol. -/
theorem smatchA_recovered_slot {Γ : Ctx S} {rest : Ctx S} {b : S.Srt}
    {tailArity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (i : Fin M.length)
    (args : Args (withMetas S M) ((M.get i).1.map (fun s => ([], s))) ((b :: rest) ++ Γ))
    (target : Term S ((b :: rest) ++ []) (M.get i).2)
    (tail : Args (withMetas S M) tailArity Γ) (targetTail : Args S tailArity [])
    (result : Term S (M.get i).1 (M.get i).2)
    (found : recoverBoundVariableBody args target = some result) :
    smatchA acc (.cons (.op (.inr (.mk i)) args) tail) (.cons target targetTail) =
      match acc.metas i with
      | none => smatchA (setMeta acc i result) tail targetTail
      | some u => if u = result then smatchA acc tail targetTail else none := by
  rw [smatchA_cons, smatchAtT, found]
  cases acc.metas i
  · rfl
  · rename_i old
    by_cases equal : old = result <;> simp [equal]

/-- Unsupported argument profiles or targets do not change the accumulator. -/
theorem smatchA_rejected_slot {Γ : Ctx S} {rest : Ctx S} {b : S.Srt}
    {tailArity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (i : Fin M.length)
    (args : Args (withMetas S M) ((M.get i).1.map (fun s => ([], s))) ((b :: rest) ++ Γ))
    (target : Term S ((b :: rest) ++ []) (M.get i).2)
    (tail : Args (withMetas S M) tailArity Γ) (targetTail : Args S tailArity [])
    (rejected : recoverBoundVariableBody args target = none) :
    smatchA acc (.cons (.op (.inr (.mk i)) args) tail) (.cons target targetTail) = none := by
  rw [smatchA_cons, smatchAtT, rejected]


/-- The old accepted binding-slot branch has exactly its original accumulator
decision and tail continuation. This covers arbitrary tails and accumulators. -/
theorem smatchA_old_prefix_branch {Γ : Ctx S} {rest : Ctx S} {b : S.Srt}
    {tailArity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (i : Fin M.length) (hb : (M.get i).1 = b :: rest)
    (args : Args (withMetas S M) ((M.get i).1.map (fun s => ([], s))) ((b :: rest) ++ Γ))
    (target : Term S ((b :: rest) ++ []) (M.get i).2)
    (tail : Args (withMetas S M) tailArity Γ) (targetTail : Args S tailArity [])
    (accepted : varArgsEq (castArgsArity (T := withMetas S M)
      (congrArg (List.map (fun s => ([], s))) hb) args)
      (prefixArgs (T := withMetas S M) (Γ := Γ) (b :: rest)) = true) :
    smatchA acc (.cons (.op (.inr (.mk i)) args) tail) (.cons target targetTail) =
      match acc.metas i with
      | none => smatchA (setMeta acc i (castTermCtx hb.symm (unScope (b :: rest) target))) tail targetTail
      | some u => if u = castTermCtx hb.symm (unScope (b :: rest) target)
          then smatchA acc tail targetTail else none := by
  exact smatchA_recovered_slot acc i args target tail targetTail _
    (recoverBoundVariableBody_old_prefix (b :: rest) _ hb target args accepted)

/-! ## The recursive injective-variable profile

This is a pattern-only domain for the algorithm, not an admission condition on
authored rules. In particular, ordinary variables have no additional restriction.
-/


mutual
/-- The recursive pattern domain of the matcher. Variables are unrestricted;
metavariables must supply a recognized injective bound-variable spine. -/
def MatchingSupportedT : {Γ : Ctx S} → (β : Ctx S) → {s : S.Srt} →
    Term (withMetas S M) (β ++ Γ) s → Prop
  | _, _, _, .var _ => True
  | _, β, _, .op (.inl _) args => MatchingSupportedA β args
  | Γ, β, _, .op (.inr (.mk i)) args =>
      ∃ projected : Args (withMetas S M) ((M.get i).1.map (fun s => ([], s))) β,
        strengthenA (Strengthener.boundPrefix (S := withMetas S M) β Γ) args =
          some projected ∧
        ∃ selected : VariableArguments projected,
          recognizeVariableArguments projected = some selected
termination_by _ _ _ pattern => 2 * termSize pattern
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

/-- Each slot extends the accumulated prefix by exactly its declared binders. -/
def MatchingSupportedA : {Γ : Ctx S} → (β : Ctx S) →
    {arity : List (List S.Srt × S.Srt)} →
    Args (withMetas S M) arity (β ++ Γ) → Prop
  | _, _, _, .nil => True
  | Γ, β, _, .cons (bs := bs) head tail =>
      MatchingSupportedT (bs ++ β)
        (castTermCtx (T := withMetas S M) (List.append_assoc bs β Γ).symm head) ∧
      MatchingSupportedA β tail
termination_by _ _ _ pattern => 2 * argsSize pattern + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

omit opDec in
theorem MExtends.setVar {Γ : Ctx S} {s : S.Srt}
    {sigma : Sub S Γ []} {body} {acc : MAcc S M Γ}
    (realizes : MExtends sigma body acc) (x : Var Γ s) :
    MExtends sigma body {acc with vars := updatePSub acc.vars x (sigma s x)} := by
  refine ⟨?_, realizes.2⟩
  intro sort y value recorded
  change updatePSub acc.vars x (sigma s x) sort y = some value at recorded
  unfold updatePSub at recorded
  split at recorded
  · next sameSort =>
      subst sameSort
      split at recorded
      · next sameVar =>
          subst sameVar
          exact Option.some.inj recorded
      · exact realizes.1 _ _ _ recorded
  · exact realizes.1 _ _ _ recorded

omit opDec [DecidableEq S.Srt] in
theorem MExtends.setMeta {Γ : Ctx S}
    {sigma : Sub S Γ []} {body} {acc : MAcc S M Γ}
    (realizes : MExtends sigma body acc) (i : Fin M.length) :
    MExtends sigma body (setMeta acc i (body i)) := by
  refine ⟨realizes.1, ?_⟩
  intro j value recorded
  simp only [_root_.Mettapedia.OSLF.Binding.setMeta] at recorded
  split at recorded
  · next same =>
      subst same
      exact Option.some.inj recorded
  · exact realizes.2 _ _ recorded

mutual
/-- Every actual instance of a supported schema is found, preserving the
same supplied closing substitution and metavariable assignment. -/
theorem smatchAtT_complete : ∀ {Γ : Ctx S} (β : Ctx S) {s : S.Srt}
    (acc : MAcc S M Γ) (pattern : Term (withMetas S M) (β ++ Γ) s)
    (target : Term S (β ++ []) s), MatchingSupportedT β pattern →
    ∀ (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2),
    MExtends sigma body acc →
    bind (liftSub sigma β) (instantiate body pattern) = target →
    ∃ acc', smatchAtT β acc pattern target = some acc' ∧ MExtends sigma body acc'
  | Γ, β, s, acc, .var x, target, supported, sigma, body, realizes, instanceEq => by
      subst target
      simp only [instantiate, bind]
      rw [smatchAtT]
      cases splitEq : splitVar β x with
      | inl v =>
          have rebuild := splitVar_recombine β x
          rw [splitEq] at rebuild
          simp only [Sum.elim_inl] at rebuild
          rw [← rebuild, liftSub_injPrefix]
          exact ⟨acc, by simp, realizes⟩
      | inr y =>
          have rebuild := splitVar_recombine β x
          rw [splitEq] at rebuild
          simp only [Sum.elim_inr] at rebuild
          rw [← rebuild, liftSub_weakenVar]
          rw [strengthenT_rename]
          cases stored : acc.vars _ y with
          | none => exact ⟨_, by simp [stored], realizes.setVar y⟩
          | some old =>
              have assigned := realizes.1 _ y old stored
              exact ⟨acc, by simp [stored, assigned], realizes⟩
  | Γ, β, _, acc, .op (.inr (.mk i)) args, target, supported, sigma, body, realizes, instanceEq => by
      subst target
      rw [MatchingSupportedT] at supported
      obtain ⟨projected, projection, selected, recognized⟩ := supported
      have recovered := (recoverBoundVariableBody_eq_some_iff args projected projection selected
        recognized _ (body i) body sigma).mpr rfl
      simp only [instantiate]
      rw [smatchAtT, recovered]
      cases stored : acc.metas i with
      | none => exact ⟨_, rfl, realizes.setMeta i⟩
      | some old =>
          have assigned := realizes.2 i old stored
          exact ⟨acc, by simp [assigned], realizes⟩
  | Γ, β, _, acc, .op (.inl f) args, target, supported, sigma, body, realizes, instanceEq => by
      subst target
      rw [MatchingSupportedT] at supported
      have child : MatchingSupportedA β args := supported
      obtain ⟨acc', found, kept⟩ := smatchAtA_complete β acc args _ child sigma body realizes rfl
      refine ⟨acc', ?_, kept⟩
      simp only [instantiate, bind]
      rw [smatchAtT]
      simpa only [↓reduceDIte] using found
termination_by _ _ _ _ pattern _ _ _ _ _ _ => 2 * termSize pattern
decreasing_by
  all_goals simp only [termSize]
  all_goals omega

theorem smatchAtA_complete : ∀ {Γ : Ctx S} (β : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (acc : MAcc S M Γ)
    (pattern : Args (withMetas S M) arity (β ++ Γ)) (target : Args S arity (β ++ [])),
    MatchingSupportedA β pattern →
    ∀ (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2),
    MExtends sigma body acc →
    bindArgs (liftSub sigma β) (instantiateArgs body pattern) = target →
    ∃ acc', smatchAtA β acc pattern target = some acc' ∧ MExtends sigma body acc'
  | Γ, β, _, acc, .nil, target, _, sigma, body, realizes, instanceEq => by
      subst target
      exact ⟨acc, by rw [instantiateArgs, bindArgs, smatchAtA], realizes⟩
  | Γ, β, _, acc, .cons (bs := bs) head tail, target, supported,
      sigma, body, realizes, instanceEq => by
      subst target
      rw [MatchingSupportedA] at supported
      obtain ⟨headSupported, tailSupported⟩ := supported
      obtain ⟨next, headMatch, headKept⟩ := smatchAtT_complete (bs ++ β) acc
        (castTermCtx (T := withMetas S M) (List.append_assoc bs β Γ).symm head)
        (castTermCtx (T := S) (List.append_assoc bs β []).symm
          (bind (liftSub (liftSub sigma β) bs) (instantiate body head)))
        headSupported sigma body realizes (by
          rw [instantiate_castTermCtx, bind_liftSub_append])
      obtain ⟨acc', tailMatch, tailKept⟩ :=
        smatchAtA_complete β next tail _ tailSupported sigma body headKept rfl
      refine ⟨acc', ?_, tailKept⟩
      simp only [instantiateArgs, bindArgs]
      rw [smatchAtA, headMatch]
      exact tailMatch
termination_by _ _ _ _ pattern _ _ _ _ _ _ => 2 * argsSize pattern + 1
decreasing_by
  all_goals simp only [termSize_castTermCtx, argsSize]
  all_goals first | omega | have := termSize_pos head; omega
end

/-- Exact adequacy for a fixed realizing assignment on the supported recursive
profile. No existence of total assignments for unused metavariables is assumed. -/
theorem smatchAtT_adequate {Γ : Ctx S} (β : Ctx S) {s : S.Srt}
    (acc : MAcc S M Γ) (pattern : Term (withMetas S M) (β ++ Γ) s)
    (target : Term S (β ++ []) s) (supported : MatchingSupportedT β pattern)
    (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc) :
    (∃ acc', smatchAtT β acc pattern target = some acc' ∧ MExtends sigma body acc') ↔
      bind (liftSub sigma β) (instantiate body pattern) = target := by
  constructor
  · rintro ⟨acc', found, kept⟩
    exact smatchAtT_sound β acc acc' pattern target found sigma body kept
  · exact smatchAtT_complete β acc pattern target supported sigma body realizes

theorem smatchAtA_adequate {Γ : Ctx S} (β : Ctx S)
    {arity : List (List S.Srt × S.Srt)} (acc : MAcc S M Γ)
    (pattern : Args (withMetas S M) arity (β ++ Γ)) (target : Args S arity (β ++ []))
    (supported : MatchingSupportedA β pattern)
    (sigma : Sub S Γ []) (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc) :
    (∃ acc', smatchAtA β acc pattern target = some acc' ∧ MExtends sigma body acc') ↔
      bindArgs (liftSub sigma β) (instantiateArgs body pattern) = target := by
  constructor
  · rintro ⟨acc', found, kept⟩
    exact smatchAtA_sound β acc acc' pattern target found sigma body kept
  · exact smatchAtA_complete β acc pattern target supported sigma body realizes

theorem smatchT_complete {Γ : Ctx S} {s : S.Srt}
    (acc : MAcc S M Γ) (pattern : Term (withMetas S M) Γ s) (target : Term S [] s)
    (supported : MatchingSupportedT [] pattern) (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc)
    (instanceEq : bind sigma (instantiate body pattern) = target) :
    ∃ acc', smatchT acc pattern target = some acc' ∧ MExtends sigma body acc' :=
  smatchAtT_complete [] acc pattern target supported sigma body realizes instanceEq

theorem smatchA_complete {Γ : Ctx S} {arity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (pattern : Args (withMetas S M) arity Γ) (target : Args S arity [])
    (supported : MatchingSupportedA [] pattern) (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc)
    (instanceEq : bindArgs sigma (instantiateArgs body pattern) = target) :
    ∃ acc', smatchA acc pattern target = some acc' ∧ MExtends sigma body acc' :=
  smatchAtA_complete [] acc pattern target supported sigma body realizes instanceEq

omit opDec [DecidableEq S.Srt] in
theorem MExtends.empty {Γ : Ctx S} (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2) :
    MExtends sigma body emptyMAcc := by
  simp [MExtends, emptyMAcc, emptyPSub]

theorem smatchT_adequate {Γ : Ctx S} {s : S.Srt}
    (acc : MAcc S M Γ) (pattern : Term (withMetas S M) Γ s) (target : Term S [] s)
    (supported : MatchingSupportedT [] pattern) (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc) :
    (∃ acc', smatchT acc pattern target = some acc' ∧ MExtends sigma body acc') ↔
      bind sigma (instantiate body pattern) = target :=
  smatchAtT_adequate [] acc pattern target supported sigma body realizes

theorem smatchA_adequate {Γ : Ctx S} {arity : List (List S.Srt × S.Srt)}
    (acc : MAcc S M Γ) (pattern : Args (withMetas S M) arity Γ) (target : Args S arity [])
    (supported : MatchingSupportedA [] pattern) (sigma : Sub S Γ [])
    (body : (i : Fin M.length) → Term S (M.get i).1 (M.get i).2)
    (realizes : MExtends sigma body acc) :
    (∃ acc', smatchA acc pattern target = some acc' ∧ MExtends sigma body acc') ↔
      bindArgs sigma (instantiateArgs body pattern) = target :=
  smatchAtA_adequate [] acc pattern target supported sigma body realizes

end Mettapedia.OSLF.Binding
