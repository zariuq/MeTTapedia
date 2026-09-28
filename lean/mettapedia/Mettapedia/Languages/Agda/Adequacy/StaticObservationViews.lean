import Mettapedia.Languages.Agda.Adequacy.StaticSpineObservation

/-!
# Constructive views of successful static observations

The views recover actual source syntax from successful observations, including
the body of a nonbinding abstraction from its weakened opening. They inspect
the option returned by the structural fold; no choice of a preimage is used.
These are syntax views, with no typing or normalization premise hidden in them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation

open Mettapedia.OSLF.Binding
open Structural (sig scope)
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody TermBody)

def termBody {n : Nat} : TermBody n → Option (StaticSpecification.Abs n)
  | .bind t => (term t).map .bind
  | .noBind t => (term t).map .noBind

theorem typeParameter_observed {n : Nat} (A : TypeParameter n)
    {a : StaticSpecification.Term n} (observed : term A.term = some a) :
    type A.code = some (.el A.level a) := by
  change (term A.term).bind (fun t => some (StaticSpecification.Ty.el A.level t)) = _
  rw [observed]
  rfl

@[simp] theorem universeTerm_observed {n : Nat} (k : Nat) :
    term (Structural.Statics.universeTerm (n := n) k) = some (.sort k) := rfl

@[simp] theorem universeType_observed (n k : Nat) :
    type (Structural.Statics.universeType n k).code = some (StaticSpecification.Ty.universe k) := rfl

theorem projection_observed {n : Nat} {s : Structural.Srt}
    (t : Term sig (scope n) s) :
    observe (bind (Telescope.projection (S := sig) .term n) t) =
      (observe t).map (Result.rename Fin.succ) := by
  exact (congrArg (@observe (n + 1) s)
    (Telescope.bind_projection (S := sig) (b := .term) t)).trans (observe_weaken t)

theorem context_snoc {n : Nat} {Γ : RawContext n} {A : RawTy n}
    {Δ : StaticSpecification.RawContext n} {a : StaticSpecification.Ty n}
    (prior : context Γ = some Δ) (entry : type A = some a) :
    context (Γ.snoc A) = some (Δ.snoc a) := by
  change (do
    let Δ ← context Γ
    let a ← type A
    pure (StaticSpecification.RawContext.snoc Δ a)) = _
  rw [prior, entry]
  rfl

theorem context_lookup {n : Nat} {Γ : RawContext n} {Δ : StaticSpecification.RawContext n}
    (observed : context Γ = some Δ) (v : Var (scope n) Structural.Srt.term) :
    type (Structural.ContextGeometry.lookup Γ v) = some (Δ.lookup (readVar v)) := by
  induction Γ with
  | nil => nomatch v
  | @snoc n Γ A ih =>
      change (do
        let Δ ← context Γ
        let a ← type A
        pure (StaticSpecification.RawContext.snoc Δ a)) = some Δ at observed
      obtain ⟨Δ', prior, rest⟩ := Option.bind_eq_some_iff.mp observed
      obtain ⟨a, entry, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      cases v with
      | zero =>
          exact (observe_weaken A).trans
            (congrArg (Option.map (StaticSpecification.Ty.rename Fin.succ)) entry)
      | succ v =>
          exact (observe_weaken (Structural.ContextGeometry.lookup Γ v)).trans
            (congrArg (Option.map (StaticSpecification.Ty.rename Fin.succ)) (ih prior v))

structure TypeBodyView {n : Nat} (B : TypeBody n) (opened : StaticSpecification.Ty (n + 1)) where
  body : StaticSpecification.TyAbs n
  observed : typeBody B = some body
  open_eq : body.open = opened

def typeBodyView {n : Nat} (B : TypeBody n) {opened : StaticSpecification.Ty (n + 1)}
    (supported : type B.open.code = some opened) : TypeBodyView B opened := by
  cases B with
  | bind A => exact ⟨.bind opened, congrArg (Option.map StaticSpecification.TyAbs.bind) supported, rfl⟩
  | noBind A =>
      change observe (bind (Telescope.projection (S := sig) .term n) A.code) = some opened at supported
      have supported := (projection_observed A.code).symm.trans supported
      change (type A.code).map StaticSpecification.Ty.weaken = some opened at supported
      cases h : type A.code with
      | none => rw [h] at supported; cases supported
      | some a =>
          have same : a.weaken = opened := Option.some.inj
            ((congrArg (Option.map StaticSpecification.Ty.weaken) h).symm.trans supported)
          exact ⟨.noBind a, congrArg (Option.map StaticSpecification.TyAbs.noBind) h, same⟩

structure TermBodyView {n : Nat} (B : TermBody n) (opened : StaticSpecification.Term (n + 1)) where
  body : StaticSpecification.Abs n
  observed : termBody B = some body
  open_eq : body.open = opened

def termBodyView {n : Nat} (B : TermBody n) {opened : StaticSpecification.Term (n + 1)}
    (supported : term B.open = some opened) : TermBodyView B opened := by
  cases B with
  | bind t => exact ⟨.bind opened, congrArg (Option.map StaticSpecification.Abs.bind) supported, rfl⟩
  | noBind t =>
      change observe (bind (Telescope.projection (S := sig) .term n) t) = some opened at supported
      have supported := (projection_observed t).symm.trans supported
      change (term t).map StaticSpecification.Term.weaken = some opened at supported
      cases h : term t with
      | none => rw [h] at supported; cases supported
      | some a =>
          have same : a.weaken = opened := Option.some.inj
            ((congrArg (Option.map StaticSpecification.Term.weaken) h).symm.trans supported)
          exact ⟨.noBind a, congrArg (Option.map StaticSpecification.Abs.noBind) h, same⟩

theorem typeBody_open_observed {n : Nat} {B : TypeBody n} {b : StaticSpecification.TyAbs n}
    (supported : typeBody B = some b) : type B.open.code = some b.open := by
  cases B with
  | bind A =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp supported
      exact ha
  | noBind A =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp supported
      change observe (bind (Telescope.projection (S := sig) .term n) A.code) = _
      exact (projection_observed A.code).trans
        (congrArg (Option.map (StaticSpecification.Ty.rename Fin.succ)) ha)

theorem termBody_lambda_observed {n : Nat} {B : TermBody n} {b : StaticSpecification.Abs n}
    (supported : termBody B = some b) : term B.lambda = some (.lam b) := by
  cases B <;> obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp supported
  · change (term _).map (fun t => StaticSpecification.Term.lam (.bind t)) = _
    rw [ha]; rfl
  · change (term _).map (fun t => StaticSpecification.Term.lam (.noBind t)) = _
    rw [ha]; rfl

theorem termBody_instantiate_observed {n : Nat} {B : TermBody n} {b : StaticSpecification.Abs n}
    {argument : RawTm n} {a : StaticSpecification.Term n}
    (body : termBody B = some b) (arg : term argument = some a) :
    term (B.instantiate argument) = some (b.instantiate a) := by
  cases B with
  | bind t =>
      obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp body
      exact observe_bind_of_some (single_observes arg) ht
  | noBind t =>
      obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.mp body
      rw [Structural.Statics.TermBody.instantiate_noBind, StaticSpecification.Abs.instantiate_noBind]
      exact ht

theorem typeBody_pi_observed {n : Nat} {A : TypeParameter n} {B : TypeBody n}
    {a : StaticSpecification.Ty n} {b : StaticSpecification.TyAbs n}
    (domain : type A.code = some a) (body : typeBody B = some b) :
    term (B.pi A) = some (.pi a b) := by
  cases B with
  | bind B =>
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp body
      change (do let a ← type A.code; let b ← type B.code; pure (StaticSpecification.Term.pi a (.bind b))) = _
      rw [domain, hb]; rfl
  | noBind B =>
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp body
      change (do let a ← type A.code; let b ← type B.code; pure (StaticSpecification.Term.pi a (.noBind b))) = _
      rw [domain, hb]; rfl

theorem app_observed {n : Nat} {f u : RawTm n} {f' u' : StaticSpecification.Term n}
    (head : term f = some f') (argument : term u = some u') :
    term (Structural.Statics.app f u) = some (f'.app u') := by
  exact eliminate_of_some head (cons_of_some (apply_of_some argument) (nil_eq (n := n)))

structure PiView {n : Nat} (A : TypeParameter n) (B : TypeBody n) (output : StaticSpecification.Ty n) where
  domain : StaticSpecification.Ty n
  body : StaticSpecification.TyAbs n
  domain_eq : type A.code = some domain
  body_eq : typeBody B = some body
  result_eq : output = StaticSpecification.Ty.pi domain body

def piView {n : Nat} (A : TypeParameter n) (B : TypeBody n) {output : StaticSpecification.Ty n}
    (supported : type (Structural.Statics.piType A B).code = some output) : PiView A B output := by
  cases B with
  | bind B =>
      change ((do
        let a ← type A.code
        let b ← type B.code
        pure (StaticSpecification.Term.pi a (.bind b)))).bind
          (fun t => some (StaticSpecification.Ty.el (max A.level B.level) t)) = some output at supported
      cases ha : type A.code with
      | none => simp only [ha] at supported; cases supported
      | some a =>
          cases hb : type B.code with
          | none => simp only [ha, hb] at supported; cases supported
          | some b =>
              have hbody : typeBody (TypeBody.bind B) = some (.bind b) := congrArg (Option.map StaticSpecification.TyAbs.bind) hb
              exact ⟨a, .bind b, ha, hbody, (Option.some.inj (supported.symm.trans (piType_observed A _ ha hbody)))⟩
  | noBind B =>
      change ((do
        let a ← type A.code
        let b ← type B.code
        pure (StaticSpecification.Term.pi a (.noBind b)))).bind
          (fun t => some (StaticSpecification.Ty.el (max A.level B.level) t)) = some output at supported
      cases ha : type A.code with
      | none => simp only [ha] at supported; cases supported
      | some a =>
          cases hb : type B.code with
          | none => simp only [ha, hb] at supported; cases supported
          | some b =>
              have hbody : typeBody (TypeBody.noBind B) = some (.noBind b) := congrArg (Option.map StaticSpecification.TyAbs.noBind) hb
              exact ⟨a, .noBind b, ha, hbody, (Option.some.inj (supported.symm.trans (piType_observed A _ ha hbody)))⟩

end Mettapedia.Languages.Agda.StaticAdequacy.Observation
