import Mettapedia.OSLF.Syntax.RhoEquationEncoding
import Mettapedia.OSLF.Syntax.RhoEquationConstructorControls

/-!
# Quotation fibres of the actual sorted rho equation classes

Quotation and drop descend independently to the authored equation quotient.
The name eta equation makes quote-after-drop the identity, but does not make
drop-after-quote the identity on processes. A closed output and its suspended
quotation give distinct process origins of the same name. Complete origin
fibres retain that distinction.

The actual unit and name eta equations also identify a name with the quote of
its own drop beside null. Thus strict syntactic descent cannot be transferred
to all equation-class decompositions by assigning a smaller size to each
recursive part. These are static equation statements, independent of whether
the separately authored operational Drop rule is admitted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoQuotationClassFibres

open RhoSchema RhoEquationConstructorControls
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

abbrev Process (context : Ctx sig) := TermQ rhoSourceE context Srt.pr

abbrev Name (context : Ctx sig) := TermQ rhoSourceE context Srt.nm

def quoteRaw {context : Ctx sig} (process : Term sig context Srt.pr) :
    Term sig context Srt.nm := .op Op.quo (.cons process .nil)

def dropRaw {context : Ctx sig} (name : Term sig context Srt.nm) :
    Term sig context Srt.pr := .op Op.drp (.cons name .nil)

def quote {context : Ctx sig} (process : Process context) : Name context :=
  Quotient.map quoteRaw (fun first second equation => by
    change EqClosure rhoSourceE first second at equation
    change EqClosure rhoSourceE (quoteRaw first) (quoteRaw second)
    exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.quo
      (.cons (bs := []) equation .nil)) process

def drop {context : Ctx sig} (name : Name context) : Process context :=
  Quotient.map dropRaw (fun first second equation => by
    change EqClosure rhoSourceE first second at equation
    change EqClosure rhoSourceE (dropRaw first) (dropRaw second)
    exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.drp
      (.cons (bs := []) equation .nil)) name

def join {context : Ctx sig} (first second : Process context) : Process context :=
  Quotient.map₂ parallel (fun first first' equation second second' equation' => by
    change EqClosure rhoSourceE first first' at equation
    change EqClosure rhoSourceE second second' at equation'
    change EqClosure rhoSourceE (parallel first second) (parallel first' second')
    exact EqClosure.cong (S := sig) (E := rhoSourceE) Op.par
      (.cons (bs := []) equation (.cons (bs := []) equation' .nil))) first second

def zero (context : Ctx sig) : Process context := project null

theorem quote_project {context : Ctx sig} (process : Term sig context Srt.pr) :
    quote (project process) = project (quoteRaw process) := rfl

theorem drop_project {context : Ctx sig} (name : Term sig context Srt.nm) :
    drop (project name) = project (dropRaw name) := rfl

theorem join_project {context : Ctx sig} (first second : Term sig context Srt.pr) :
    join (project first) (project second) = project (parallel first second) := rfl

def closeName {context : Ctx sig} (name : Term sig context Srt.nm) :
    Sub sig [Srt.nm] context
  | _, .zero => name

theorem quote_drop_raw {context : Ctx sig} (name : Term sig context Srt.nm) :
    EqClosure rhoSourceE (quoteRaw (dropRaw name)) name :=
  EqClosure.ax_closed (E := rhoSourceE) (Γ := context) 3 contDiscard (closeName name)

theorem quote_drop {context : Ctx sig} (name : Name context) : quote (drop name) = name := by
  induction name using Quotient.inductionOn with
  | _ name => exact Quotient.sound (quote_drop_raw name)

theorem join_zero_right {context : Ctx sig} (process : Process context) :
    join process (zero context) = process := by
  induction process using Quotient.inductionOn with
  | _ process => exact Quotient.sound (parallel_null_equation process)

def closePair {context : Ctx sig} (first second : Term sig context Srt.pr) :
    Sub sig [Srt.pr, Srt.pr] context
  | _, .zero => first
  | _, .succ .zero => second

theorem parallel_commutes {context : Ctx sig} (first second : Term sig context Srt.pr) :
    EqClosure rhoSourceE (parallel first second) (parallel second first) :=
  EqClosure.ax_closed (E := rhoSourceE) (Γ := context) 0 contDiscard (closePair first second)

theorem join_commutes {context : Ctx sig} (first second : Process context) :
    join first second = join second first := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second => exact Quotient.sound (parallel_commutes first second)

theorem join_zero_left {context : Ctx sig} (process : Process context) :
    join (zero context) process = process :=
  (join_commutes _ _).trans (join_zero_right process)

theorem own_drop_beside_zero {context : Ctx sig} (name : Name context) :
    quote (join (drop name) (zero context)) = name := by
  rw [join_zero_right, quote_drop]

theorem no_strict_descent_on_all_class_decompositions (context : Ctx sig) :
    ¬ ∃ measure : Name context → Nat,
      ∀ name, measure name < measure (quote (join (drop name) (zero context))) := by
  rintro ⟨measure, descends⟩
  have smaller := descends (quote (zero context))
  rw [own_drop_beside_zero] at smaller
  exact (Nat.lt_irrefl _) smaller

def Origin {context : Ctx sig} (name : Name context) :=
  {process : Process context // quote process = name}

def visible : Process [] := project RhoSourceOutputPredicate.output

def suspended : Process [] := drop (quote visible)

def suspendedRaw : Term sig [] Srt.pr := dropRaw (quoteRaw RhoSourceOutputPredicate.output)

theorem suspended_project : suspended = project suspendedRaw := rfl

theorem suspended_not_visible : suspended ≠ visible := by
  intro equal
  have encoded := congrArg RhoSchema.IntrinsicEncoding.encodeEquationClass equal
  change canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm suspendedRaw) =
    canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm RhoSourceOutputPredicate.output) at encoded
  have different : canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm suspendedRaw) ≠
      canonicalize (RhoSchema.IntrinsicEncoding.encodeTerm RhoSourceOutputPredicate.output) := by
    decide +kernel
  exact different encoded

theorem same_actual_name : quote suspended = quote visible := quote_drop (quote visible)

theorem quotation_not_injective : ¬ Function.Injective (quote : Process [] → Name []) :=
  fun injective => suspended_not_visible (injective same_actual_name)

/-- Name equality forgets which process was quoted. Recovering every process
origin therefore requires more than the name class alone. -/
theorem no_name_only_activation_recovers_every_origin :
    ¬ ∃ activate : Name [] → Process [], ∀ process : Process [], activate (quote process) = process := by
  rintro ⟨activate, recovers⟩
  apply quotation_not_injective
  intro first second same
  exact (recovers first).symm.trans ((congrArg activate same).trans (recovers second))

def visibleOrigin : Origin (quote visible) := ⟨visible, rfl⟩

def suspendedOrigin : Origin (quote visible) := ⟨suspended, same_actual_name⟩

theorem actual_origins_distinct : visibleOrigin ≠ suspendedOrigin := by
  intro same
  exact suspended_not_visible (congrArg Subtype.val same).symm

theorem not_all_origin_fibres_subsingleton :
    ¬ ∀ name : Name [], Subsingleton (Origin name) := by
  intro unique
  exact actual_origins_distinct (@Subsingleton.elim _ (unique (quote visible)) _ _)

theorem process_beta_not_a_source_equation :
    ¬ ∀ process : Process [], drop (quote process) = process :=
  fun beta => suspended_not_visible (beta visible)

end Mettapedia.OSLF.Binding.RhoQuotationClassFibres
