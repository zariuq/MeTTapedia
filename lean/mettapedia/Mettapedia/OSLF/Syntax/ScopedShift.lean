import Mettapedia.OSLF.Syntax.PatternAsBindingSignature
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# The engine's shift is a weakening, and it is the only one that fits

Rule firing shifts a matched value by the difference between the depth at which
the left-hand side captured it and the depth at which the right-hand side uses
it.  Written on the untyped syntax that is an arithmetic choice, and an
arithmetic choice needs a reason.

The reason is that the shift is not a choice at all: it is the erasure of
weakening in the intrinsically scoped presentation, where a value matched `dc`
binders deep lives in a context of `dc` sorts and using it `d` deep means
moving it into a context of `d`.  `erase_weakenBy` is that statement.

`shift_amount_unique` then characterises the amount: a shift agrees with the
scoped weakening on every value exactly when it is `d - dc`.  Commutation with
erasure is the right statement of capture-avoidance, because it says the
delivered term *denotes the same variable* -- and scoping cannot say that.

That is worth being precise about, because the obvious argument does not work.
Well-scopedness of the delivered value is only **soundness**: it bounds the
amount from above and not from below, since a value matched one binder deep and
delivered unshifted two binders deep is still well-scoped there.  That unshifted
delivery is exactly the capturing one, and `wellScoped_does_not_bound_below`
records that the scoping test admits it.  So:

* `delivered_isWellScopedAt` -- soundness: the delivered value is well-scoped
  where it is delivered.
* `larger_shift_breaks_scope` -- there is a value, the innermost variable, whose
  scope any larger shift breaks.
* `shift_amount_unique` -- the characterisation, and the only one of the three
  that is two-sided.

This is the transport direction the scoped layer exists for.  Well-scopedness
and the lifting laws are proved once, on the indexed family where they are
cheap, and reach the untyped engine through erasure instead of being proved a
second time on `Pattern`.
-/

namespace Mettapedia.OSLF.Binding.PatternPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match

set_option autoImplicit false

/-! ## Weakening by an arbitrary number of binders -/

/-- Weakening past `k` binders. -/
def weakenBy : (k : Nat) → {Γ : Ctx patSig} → Ren patSig Γ (ctxOf k ++ Γ)
  | 0, _ => fun _ v => v
  | k + 1, _ => fun s v => Var.succ (weakenBy k s v)

theorem varIndex_weakenBy : ∀ (k : Nat) {Γ : Ctx patSig} {s : PatSrt} (v : Var Γ s),
    varIndex (weakenBy k s v) = varIndex v + k
  | 0, _, _, _ => rfl
  | k + 1, _, _, v => by
      show varIndex (weakenBy k _ v) + 1 = varIndex v + (k + 1)
      rw [varIndex_weakenBy k v]
      omega

theorem shiftsAtBy_weakenBy (k : Nat) {Γ : Ctx patSig} :
    ShiftsAtBy (weakenBy k (Γ := Γ)) 0 k := by
  intro s v
  simp [varIndex_weakenBy k v]

/-- **The engine's shift is the erasure of the scoped weakening.**  Lifting
de Bruijn indices by `k` on a pattern is what weakening past `k` binders does to
the term it erases from. -/
theorem erase_weakenBy (k : Nat) {Γ : Ctx patSig} {s : PatSrt} (t : Term patSig Γ s) :
    erase (rename (weakenBy k) t) = liftBVars 0 k (erase t) :=
  erase_rename_shiftBy _ 0 k (shiftsAtBy_weakenBy k) t

/-! ## What scoping does and does not settle -/

/-- **Soundness of the delivery.**  A value matched `dc` binders deep and
delivered `d` deep is well-scoped at `d`.  This is not sharpness: see
`wellScoped_does_not_bound_below`. -/
theorem delivered_isWellScopedAt {dc d : Nat} (hle : dc ≤ d)
    (v : Term patSig (ctxOf dc) PatSrt.pat) :
    (liftBVars 0 (d - dc) (erase v)).isWellScopedAt d = true := by
  have hv : (erase v).isWellScopedAt dc = true := by
    simpa using erase_isWellScopedAt v
  have hlift := liftBVars_isWellScopedAt (ambient := dc) (cutoff := 0)
    (shift := d - dc) (by simpa using hv)
  simpa [Nat.add_sub_cancel' hle] using hlift

/-- The variable naming the innermost of `dc` binders: the value most sensitive
to the amount of the shift. -/
def topVar (dc : Nat) (h : 0 < dc) : Term patSig (ctxOf dc) PatSrt.pat :=
  Term.var (varOfFin ⟨dc - 1, by omega⟩)

theorem erase_topVar (dc : Nat) (h : 0 < dc) :
    erase (topVar dc h) = Pattern.bvar (dc - 1) := by
  show Pattern.bvar (varIndex (varOfFin ⟨dc - 1, by omega⟩)) = _
  rw [varIndex_varOfFin]

theorem liftBVars_bvar_zero_cutoff (j n : Nat) :
    liftBVars 0 j (Pattern.bvar n) = Pattern.bvar (n + j) := by
  simp [liftBVars]

/-- **A larger shift breaks some value's scope.**  The witness is the innermost
variable; a ground value survives any shift, so this is existential and not
universal in the value. -/
theorem larger_shift_breaks_scope {dc d j : Nat} (hpos : 0 < dc) (hle : dc ≤ d)
    (hbig : d - dc < j) :
    (liftBVars 0 j (erase (topVar dc hpos))).isWellScopedAt d = false := by
  rw [erase_topVar, liftBVars_bvar_zero_cutoff]
  simp only [Pattern.isWellScopedAt, decide_eq_false_iff_not, Nat.not_lt]
  omega

/-- **Scoping cannot bound the shift from below.**  A value matched one binder
deep and delivered *unshifted* two binders deep is still well-scoped there --
and that unshifted delivery is precisely the capturing one.  So well-scopedness
is the wrong test for capture-avoidance, and the characterisation below is
stated as commutation with erasure instead. -/
theorem wellScoped_does_not_bound_below :
    (liftBVars 0 0 (erase (topVar 1 (by omega)))).isWellScopedAt 2 = true := by decide

/-- **The amount is the only one that commutes with erasure.**  A shift agrees
with the scoped weakening on every value exactly when it is the difference of
depths: smaller and the delivered term names the binder the rule introduced,
larger and it names one that does not exist.  This is capture-avoidance stated
as what it is -- the delivered term denotes the same variable -- rather than as
a bound on indices. -/
theorem shift_amount_unique {dc d j : Nat} (hpos : 0 < dc) :
    (∀ v : Term patSig (ctxOf dc) PatSrt.pat,
        liftBVars 0 j (erase v) = erase (rename (weakenBy (d - dc)) v))
      ↔ j = d - dc := by
  constructor
  · intro h
    have hv := h (topVar dc hpos)
    rw [erase_weakenBy, erase_topVar, liftBVars_bvar_zero_cutoff,
      liftBVars_bvar_zero_cutoff] at hv
    injection hv with hv
    omega
  · rintro rfl v
    exact (erase_weakenBy _ v).symm

/-! ## The applier computes in the scoped world

The two theorems above are about the shift in isolation.  These say the engine
performs it: at a metavariable occurrence, what rule firing delivers *is* the
erasure of the scoped weakening of the matched value, and it is therefore
well-scoped where it is delivered.

This is the metavariable case -- the one the capture defect lived in.  The
collection rest variable is delivered the same way, each spliced element being
weakened by the same difference of depths, so the same pair of statements
covers it once the sequence sort is folded into this presentation. -/

/-- **Rule firing delivers the erasure of a scoped weakening.**  The applier's
metavariable case is not an arithmetic manipulation of de Bruijn indices that
happens to be right; it is the erasure of moving a term from the context it was
matched in to the context it is used in. -/
theorem applyBindingsScoped_fvar_is_weakening
    (lhs : Pattern) (x : String) (dc d : Nat)
    (v : Term patSig (ctxOf dc) PatSrt.pat) (bindings : Bindings)
    (found : bindings.find? (fun entry => entry.1 == x) = some (x, erase v))
    (hcap : captureDepth x 0 lhs = some dc) :
    applyBindingsScoped lhs bindings d (.fvar x)
      = erase (rename (weakenBy (d - dc)) v) := by
  rw [erase_weakenBy]
  simp only [applyBindingsScoped, found, hcap]

/-- **So what rule firing delivers is well-scoped where it is delivered.**  This
is the engine's half of scope preservation, obtained by transport from the
indexed family rather than by a second induction over `Pattern`. -/
theorem applyBindingsScoped_fvar_isWellScopedAt
    (lhs : Pattern) (x : String) {dc d : Nat} (hle : dc ≤ d)
    (v : Term patSig (ctxOf dc) PatSrt.pat) (bindings : Bindings)
    (found : bindings.find? (fun entry => entry.1 == x) = some (x, erase v))
    (hcap : captureDepth x 0 lhs = some dc) :
    (applyBindingsScoped lhs bindings d (.fvar x)).isWellScopedAt d = true := by
  rw [applyBindingsScoped_fvar_is_weakening lhs x dc d v bindings found hcap,
    erase_weakenBy]
  exact delivered_isWellScopedAt hle v

end Mettapedia.OSLF.Binding.PatternPresentation
