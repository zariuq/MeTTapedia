import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.UnifyingFrames

/-!
# Source support and current-substitution effects

An effect scope bounds both the variables a source region can observe and
the variables its unifiers may update. Current substitutions must be closed
on that finite scope. Retained observations are tested after substitution,
so differently named recipes that alias are not mistaken for disjoint data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameEffects

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions UnifyingFrames

theorem support_expression (values : List Atom) (x : String) :
    x ∈ support (.expression values) ↔ ∃ value ∈ values, x ∈ support value := by
  rw [support, UnifyAtoms.encode_expression,
    Mettapedia.Logic.LP.Term.mem_freeVars_app (σ := UnifyAtoms.sig)]
  constructor
  · rintro ⟨i, member⟩
    exact ⟨values.get i, List.get_mem _ _, member⟩
  · rintro ⟨value, present, member⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp present
    exact ⟨i, member⟩

theorem support_subst (σ : Substitution) (value : Atom) (x : String) :
    x ∈ support (substA σ value) ↔ ∃ y ∈ support value, x ∈ support (σ y) := by
  induction value using Atom.rec
    (motive_2 := fun values => ∀ value ∈ values,
      x ∈ support (substA σ value) ↔ ∃ y ∈ support value, x ∈ support (σ y)) with
  | var name => simp [substA, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | symbol _ => simp [substA, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | grounded _ => simp [substA, support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars]
  | expression values ih =>
      rw [substA, UnifyAtoms.substL_eq_map, support_expression]
      constructor
      · rintro ⟨mapped, present, occurs⟩
        obtain ⟨value, member, rfl⟩ := List.mem_map.mp present
        obtain ⟨y, source, image⟩ := (ih value member).mp occurs
        exact ⟨y, (support_expression values y).mpr ⟨value, member, source⟩, image⟩
      · rintro ⟨y, source, image⟩
        obtain ⟨value, member, occurs⟩ := (support_expression values y).mp source
        exact ⟨substA σ value, List.mem_map.mpr ⟨value, member, rfl⟩,
          (ih value member).mpr ⟨y, occurs, image⟩⟩
  | nil value member => cases member
  | cons head rest ihHead ihRest value member =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ihHead
      · exact ihRest value member

def Closed (scope : Finset String) (σ : Substitution) : Prop :=
  ∀ x ∈ scope, support (σ x) ⊆ scope

def closureCheck (scope : Finset String) (σ : Substitution) : Bool :=
  decide (∀ x ∈ scope, support (σ x) ⊆ scope)

theorem closureCheck_iff (scope : Finset String) (σ : Substitution) :
    closureCheck scope σ = true ↔ Closed scope σ := by
  simp [closureCheck, Closed]

theorem subst_support_subset {scope : Finset String} {σ : Substitution}
    (closed : Closed scope σ) {value : Atom} (supported : support value ⊆ scope) :
    support (substA σ value) ⊆ scope := by
  intro x member
  obtain ⟨y, occurs, image⟩ := (support_subst σ value x).mp member
  exact closed y (supported occurs) image

theorem subst_fixes (σ : Substitution) (value : Atom)
    (fixed : ∀ x ∈ support value, σ x = .var x) : substA σ value = value := by
  have encoded := Mettapedia.Logic.LP.Subst.applyTerm_eq_self (σ := UnifyAtoms.sig)
    (θ := fun x => UnifyAtoms.encode (σ x)) (t := UnifyAtoms.encode value)
    (fun x member => by rw [fixed x member, UnifyAtoms.encode])
  have decoded := congrArg UnifyAtoms.decode encoded
  rw [UnifyAtoms.decode_applyTerm (fun x => UnifyAtoms.encode (σ x)) value,
    UnifyAtoms.decode_encode] at decoded
  have same : (fun x => UnifyAtoms.decode (UnifyAtoms.encode (σ x))) = σ := by
    funext x
    exact UnifyAtoms.decode_encode _
  rw [same] at decoded
  exact decoded

structure Local (scope : Finset String) (σ : Substitution) : Prop where
  closed : Closed scope σ
  fixes : ∀ x, x ∉ scope → σ x = .var x

theorem Local.identity (scope : Finset String) : Local scope Atom.var where
  closed x hx := by simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using hx
  fixes _ _ := rfl

theorem Local.compose {scope : Finset String} {σ τ : Substitution}
    (first : Local scope σ) (second : Local scope τ) : Local scope (compose τ σ) where
  closed x hx := subst_support_subset second.closed (first.closed x hx)
  fixes x hx := by
    change substA τ (σ x) = _
    rw [first.fixes x hx, substA, second.fixes x hx]

/-- Only the update is required to be local; an incoming environment may
contain unrelated interpreted values or aliases. -/
def Effect (scope : Finset String) (before after : Substitution) : Prop :=
  ∃ update, Local scope update ∧ after = compose update before

theorem Effect.refl (scope : Finset String) (σ : Substitution) : Effect scope σ σ := by
  refine ⟨Atom.var, Local.identity scope, ?_⟩
  funext x
  exact (substA_var_self (σ x)).symm

theorem Effect.trans {scope : Finset String} {σ τ υ : Substitution}
    (first : Effect scope σ τ) (second : Effect scope τ υ) : Effect scope σ υ := by
  obtain ⟨a, ha, rfl⟩ := first
  obtain ⟨b, hb, rfl⟩ := second
  refine ⟨compose b a, ha.compose hb, ?_⟩
  funext x
  exact substA_compose b a (σ x)

theorem Effect.closed {scope : Finset String} {σ τ : Substitution}
    (changed : Effect scope σ τ) (before : Closed scope σ) : Closed scope τ := by
  obtain ⟨update, locality, rfl⟩ := changed
  intro x member
  exact subst_support_subset locality.closed (before x member)

theorem Effect.toLocal {scope : Finset String} {σ τ : Substitution}
    (changed : Effect scope σ τ) (before : Local scope σ) : Local scope τ := by
  obtain ⟨update, locality, rfl⟩ := changed
  exact before.compose locality

theorem Effect.preserves {scope : Finset String} {σ τ : Substitution}
    (changed : Effect scope σ τ) (frame : Atom)
    (separate : Disjoint (observedSupport σ frame) scope) :
    substA τ frame = substA σ frame := by
  obtain ⟨update, locality, rfl⟩ := changed
  rw [← substA_compose]
  apply subst_fixes
  intro x member
  exact locality.fixes x fun hx => Finset.disjoint_left.mp separate member hx

theorem support_decode_subset (term : Mettapedia.Logic.LP.Term UnifyAtoms.sig) :
    support (UnifyAtoms.decode term) ⊆ term.freeVars := by
  induction term with
  | var _ => simp [UnifyAtoms.decode, support, UnifyAtoms.encode]
  | const leaf => cases leaf <;> simp [UnifyAtoms.decode, support, UnifyAtoms.encode,
      Mettapedia.Logic.LP.Term.freeVars]
  | app n children ih =>
      intro x member
      obtain ⟨value, present, occurs⟩ := (support_expression _ x).mp member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp present
      exact (Mettapedia.Logic.LP.Term.mem_freeVars_app (σ := UnifyAtoms.sig)).mpr ⟨i, ih i occurs⟩

theorem unify_local {pattern value : Atom} {theta : Mettapedia.Logic.LP.Subst UnifyAtoms.sig}
    {scope : Finset String} (unified : UnifyAtoms.unify pattern value = some theta)
    (supported : support pattern ∪ support value ⊆ scope) :
    Local scope (UnifyAtoms.readBack theta) := by
  have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent
    [(UnifyAtoms.encode pattern, UnifyAtoms.encode value)] theta unified
  have enlarged := relevant.mono (show Mettapedia.Logic.LP.eqVars
    [(UnifyAtoms.encode pattern, UnifyAtoms.encode value)] ⊆ scope by
      simpa [Mettapedia.Logic.LP.eqVars] using supported)
  refine ⟨fun x member => (support_decode_subset (theta x)).trans (enlarged.range x member), ?_⟩
  intro x outside
  simp only [UnifyAtoms.readBack, enlarged.fixes x outside, UnifyAtoms.decode]

theorem bindPattern_effect {scope : Finset String} {σ τ : Substitution} {pattern : Pat} {value : Atom}
    (bound : bindPattern σ pattern value = some τ)
    (supported : bindSupport σ pattern value ⊆ scope) : Effect scope σ τ := by
  unfold bindPattern at bound
  cases unified : UnifyAtoms.unify (substA σ pattern.toAtom) (substA σ value) with
  | none => simp [unified] at bound
  | some theta =>
      refine ⟨UnifyAtoms.readBack theta, unify_local unified supported, ?_⟩
      exact (Option.some.inj (by simpa only [unified, Option.map_some] using bound)).symm

mutual
/-- The source dependence checker accepts only the supported pure syntax.
All names are checked against an explicit finite effect scope. -/
def check (scope : Finset String) : Expr → Bool
  | .var x => decide (x ∈ scope)
  | .const value => decide (support value ⊆ scope)
  | .ctor _ args => checkAll scope args
  | .self [arg] => check scope arg
  | .letE pattern value body => decide (support pattern.toAtom ⊆ scope) &&
      check scope value && check scope body
  | .ifE condition yes no => check scope condition && check scope yes && check scope no
  | .empty => true
  | _ => false

def checkAll (scope : Finset String) : List Expr → Bool
  | [] => true
  | e :: es => check scope e && checkAll scope es
end

theorem checkAll_iff (scope : Finset String) : ∀ es : List Expr,
    checkAll scope es = true ↔ ∀ e ∈ es, check scope e = true
  | [] => by simp [checkAll]
  | e :: es => by simp [checkAll, checkAll_iff scope es]

def frameCheck (scope : Finset String) (σ : Substitution) (frames : List Atom) : Bool :=
  frames.all fun frame => decide (Disjoint (observedSupport σ frame) scope)

theorem frameCheck_iff (scope : Finset String) (σ : Substitution) (frames : List Atom) :
    frameCheck scope σ frames = true ↔ ∀ frame ∈ frames, Disjoint (observedSupport σ frame) scope := by
  simp [frameCheck, List.all_eq_true]

def ScopedOracle (Γ : Decls) (scope : Finset String) (oracle : SelfOracle) : Prop :=
  ∀ value, Uninterp Γ value → support value ⊆ scope →
    ∀ result ∈ oracle [value], Uninterp Γ result ∧ support result ⊆ scope

structure ScopedGood (Γ : Decls) (scope : Finset String) (before : Substitution)
    (out : Outcome) : Prop where
  data : Uninterp Γ out.1
  supported : support out.1 ⊆ scope
  clean : Clean Γ out.2
  closed : Closed scope out.2
  extension : Extends Γ before out.2
  effect : Effect scope before out.2

structure ScopedGoodList (Γ : Decls) (scope : Finset String) (before : Substitution)
    (out : List Atom × Substitution) : Prop where
  data : ∀ value ∈ out.1, Uninterp Γ value
  supported : ∀ value ∈ out.1, support value ⊆ scope
  clean : Clean Γ out.2
  closed : Closed scope out.2
  extension : Extends Γ before out.2
  effect : Effect scope before out.2

theorem evalAll_scoped {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (oracle : SelfOracle) (es : List Expr)
    (each : ∀ e ∈ es, ∀ σ, Clean Γ σ → Closed scope σ →
      ∀ out ∈ evalUnifying fallback oracle e σ, ScopedGood Γ scope σ out) :
    ∀ σ, Clean Γ σ → Closed scope σ →
      ∀ out ∈ evalAllUnifying fallback oracle es σ, ScopedGoodList Γ scope σ out := by
  induction es with
  | nil =>
      intro σ clean closed out member
      have eq : out = ([], σ) := by simpa [evalAllUnifying] using member
      subst out
      exact ⟨by simp, by simp, clean, closed, Extends.refl Γ σ, Effect.refl scope σ⟩
  | cons e es ih =>
      intro σ clean closed out member
      simp only [evalAllUnifying, Multiset.mem_bind, Multiset.mem_map] at member
      obtain ⟨first, hf, rest, hr, rfl⟩ := member
      have firstGood := each e (by simp) σ clean closed first hf
      have restGood := ih (fun a ha => each a (by simp [ha]))
        first.2 firstGood.clean firstGood.closed rest hr
      refine ⟨?_, ?_, restGood.clean, restGood.closed,
        firstGood.extension.trans restGood.extension, firstGood.effect.trans restGood.effect⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact firstGood.data
        · exact restGood.data a ha
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact firstGood.supported
        · exact restGood.supported a ha

/-- The syntax check derives a full-run effect invariant, not just a law
about one binding. Recursive answers must remain in the admitted scope. -/
theorem accepted_scoped {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (oracle : SelfOracle) (oracleGood : ScopedOracle Γ scope oracle)
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true) :
    ∀ σ, Clean Γ σ → Closed scope σ →
      ∀ out ∈ evalUnifying fallback oracle e σ, ScopedGood Γ scope σ out := by
  induction accepted with
  | var x =>
      intro σ clean closed out member
      have eq : out = (.var x, σ) := by simpa [evalUnifying] using member
      subst out
      refine ⟨trivial, ?_, clean, closed, Extends.refl Γ σ, Effect.refl scope σ⟩
      simpa [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] using
        (of_decide_eq_true checked : x ∈ scope)
  | const a data =>
      intro σ clean closed out member
      have eq : out = (a, σ) := by simpa [evalUnifying] using member
      subst out
      exact ⟨data, of_decide_eq_true checked, clean, closed, Extends.refl Γ σ, Effect.refl scope σ⟩
  | @ctor c args head parts ih =>
      intro σ clean closed out member
      simp only [evalUnifying, Multiset.mem_map] at member
      obtain ⟨values, hv, rfl⟩ := member
      have good := evalAll_scoped fallback oracle args
        (fun a ha => ih a ha ((checkAll_iff scope args).mp checked a ha)) σ clean closed values hv
      refine ⟨UnifyAtoms.uninterp_of_all ?_, ?_, good.clean, good.closed, good.extension, good.effect⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact head
        · exact good.data a ha
      · intro x hx
        obtain ⟨a, ha, hx⟩ := (support_expression _ x).mp hx
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [support, UnifyAtoms.encode, Mettapedia.Logic.LP.Term.freeVars] at hx
        · exact good.supported a ha hx
  | @self arg argument ih =>
      intro σ clean closed out member
      simp only [evalUnifying, evalAllUnifying,
        Multiset.mem_bind, Multiset.mem_map, Multiset.mem_singleton] at member
      obtain ⟨values, hvalues, value, hv, rfl⟩ := member
      obtain ⟨first, hf, tail, htail, htailEq⟩ := hvalues
      subst tail
      subst values
      have good := ih checked σ clean closed first hf
      have result := oracleGood _ (uninterp_substA good.clean _ good.data)
        (subst_support_subset good.closed good.supported) value hv
      exact ⟨result.1, result.2, good.clean, good.closed, good.extension, good.effect⟩
  | @letE p val body pattern value result ihv ihb =>
      have checks : (support p.toAtom ⊆ scope ∧ check scope val = true) ∧
          check scope body = true := by simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using checked
      intro σ clean closed out member
      simp only [evalUnifying, Multiset.mem_bind] at member
      obtain ⟨first, hf, member⟩ := member
      have good := ihv checks.1.2 σ clean closed first hf
      cases bound : bindPattern first.2 p first.1 with
      | none => simp [bound] at member
      | some τ =>
          rw [bound] at member
          have changed := bindPattern_effect bound (Finset.union_subset
            (subst_support_subset good.closed checks.1.1)
            (subst_support_subset good.closed good.supported))
          have sound := bindPattern_sound good.clean pattern good.data bound
          have final := ihb checks.2 τ sound.1 (changed.closed good.closed) out member
          exact ⟨final.data, final.supported, final.clean, final.closed,
            good.extension.trans (sound.2.1.trans final.extension),
            good.effect.trans (changed.trans final.effect)⟩
  | @ifE c t e condition yes no ihc iht ihe =>
      have checks : (check scope c = true ∧ check scope t = true) ∧ check scope e = true :=
        by simpa only [check, Bool.and_eq_true] using checked
      intro σ clean closed out member
      simp only [evalUnifying, Multiset.mem_bind] at member
      obtain ⟨first, hf, member⟩ := member
      have good := ihc checks.1.1 σ clean closed first hf
      split at member
      · have final := iht checks.1.2 first.2 good.clean good.closed out member
        exact ⟨final.data, final.supported, final.clean, final.closed,
          good.extension.trans final.extension, good.effect.trans final.effect⟩
      · have final := ihe checks.2 first.2 good.clean good.closed out member
        exact ⟨final.data, final.supported, final.clean, final.closed,
          good.extension.trans final.extension, good.effect.trans final.effect⟩
  | empty =>
      intro σ clean closed out member
      exact False.elim (Multiset.notMem_zero out member)

/-- Every admitted run preserves every currently disjoint observation,
including observations with variables and declared constructors. -/
theorem checked_run_preserves_frames {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (oracle : SelfOracle) (oracleGood : ScopedOracle Γ scope oracle)
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true)
    {σ : Substitution} (clean : Clean Γ σ) (closed : closureCheck scope σ = true)
    (frames : List Atom) (separate : frameCheck scope σ frames = true)
    {out : Outcome} (member : out ∈ evalUnifying fallback oracle e σ) :
    frames.map (substA out.2) = frames.map (substA σ) := by
  have good := accepted_scoped fallback oracle oracleGood accepted checked σ clean
    ((closureCheck_iff scope σ).mp closed) out member
  exact List.map_congr_left fun frame hf =>
    good.effect.preserves frame ((frameCheck_iff scope σ frames).mp separate frame hf)

theorem evalAll_scoped_congr {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (o o' : SelfOracle) (es : List Expr)
    (same : ∀ e ∈ es, ∀ σ, Clean Γ σ → Closed scope σ →
      evalUnifying fallback o e σ = evalUnifying fallback o' e σ)
    (sound : ∀ e ∈ es, ∀ σ, Clean Γ σ → Closed scope σ →
      ∀ out ∈ evalUnifying fallback o e σ, ScopedGood Γ scope σ out) :
    ∀ σ, Clean Γ σ → Closed scope σ →
      evalAllUnifying fallback o es σ = evalAllUnifying fallback o' es σ := by
  induction es with
  | nil => intro σ _ _; rfl
  | cons e es ih =>
      intro σ clean closed
      simp only [evalAllUnifying]
      rw [← same e (by simp) σ clean closed]
      apply Multiset.bind_congr
      intro first member
      have good := sound e (by simp) σ clean closed first member
      rw [ih (fun e he => same e (by simp [he]))
        (fun e he => sound e (by simp [he])) first.2 good.clean good.closed]

/-- Oracle equivalence is needed only at clean, scope-supported calls
actually justified by the source checker. -/
theorem accepted_scoped_congr {Γ : Decls} {scope : Finset String}
    (fallback : Fallback) (o o' : SelfOracle) (oracleGood : ScopedOracle Γ scope o)
    (agree : ∀ value, Uninterp Γ value → support value ⊆ scope → o [value] = o' [value])
    {e : Expr} (accepted : UnifyingRegions.Accepted Γ e) (checked : check scope e = true) :
    ∀ σ, Clean Γ σ → Closed scope σ →
      evalUnifying fallback o e σ = evalUnifying fallback o' e σ := by
  induction accepted with
  | var => intro σ _ _; rfl
  | const => intro σ _ _; rfl
  | @ctor c args head parts ih =>
      intro σ clean closed
      have checks := (checkAll_iff scope args).mp checked
      simp only [evalUnifying]
      rw [evalAll_scoped_congr fallback o o' args (fun a ha => ih a ha (checks a ha))
        (fun a ha => accepted_scoped fallback o oracleGood (parts a ha) (checks a ha)) σ clean closed]
  | @self arg argument ih =>
      intro σ clean closed
      have sameAll := evalAll_scoped_congr fallback o o' [arg]
        (fun e he => by simp only [List.mem_singleton] at he; subst e; exact ih checked)
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_scoped fallback o oracleGood argument checked) σ clean closed
      simp only [evalUnifying]
      rw [← sameAll]
      apply Multiset.bind_congr
      intro out member
      have good := evalAll_scoped fallback o [arg]
        (fun e he => by
          simp only [List.mem_singleton] at he
          subst e
          exact accepted_scoped fallback o oracleGood argument checked) σ clean closed out member
      obtain ⟨v, shape⟩ := List.length_eq_one_iff.mp (evalAll_length fallback o [arg] σ out member)
      have data := good.data v (by simp [shape])
      have supported := good.supported v (by simp [shape])
      rw [shape]
      simp only [List.map_cons, List.map_nil]
      rw [agree _ (uninterp_substA good.clean v data) (subst_support_subset good.closed supported)]
  | @letE p val body pattern value result ihv ihb =>
      have checks : (support p.toAtom ⊆ scope ∧ check scope val = true) ∧
          check scope body = true := by simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using checked
      intro σ clean closed
      simp only [evalUnifying]
      rw [← ihv checks.1.2 σ clean closed]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_scoped fallback o oracleGood value checks.1.2 σ clean closed first member
      cases bound : bindPattern first.2 p first.1 with
      | none => rfl
      | some τ =>
          have changed := bindPattern_effect bound (Finset.union_subset
            (subst_support_subset good.closed checks.1.1)
            (subst_support_subset good.closed good.supported))
          exact ihb checks.2 τ (bindPattern_sound good.clean pattern good.data bound).1
            (changed.closed good.closed)
  | @ifE c t e condition yes no ihc iht ihe =>
      have checks : (check scope c = true ∧ check scope t = true) ∧ check scope e = true :=
        by simpa only [check, Bool.and_eq_true] using checked
      intro σ clean closed
      simp only [evalUnifying]
      rw [← ihc checks.1.1 σ clean closed]
      apply Multiset.bind_congr
      intro first member
      have good := accepted_scoped fallback o oracleGood condition checks.1.1 σ clean closed first member
      split
      · exact iht checks.1.2 first.2 good.clean good.closed
      · exact ihe checks.2 first.2 good.clean good.closed
  | empty => intro σ _ _; rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFrameEffects
