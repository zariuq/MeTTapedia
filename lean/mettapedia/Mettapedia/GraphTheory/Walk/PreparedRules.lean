import Mettapedia.GraphTheory.Walk.NativeTypeTheory
import Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation

/-!
# Prepared execution of the authored graph-walk rules

Use the existing first-order rule compiler on the graph-walk LanguageDef.
Adjacency and the vertex map remain the declared relation inputs. The
compiled frontier keeps the order and multiplicity of the authored rules.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Walk.PreparedRules

open Mettapedia.GraphTheory.Walk.LanguageDef
open Mettapedia.GraphTheory.Walk.NativeTypeTheory
open Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Syntax
open SimpleGraph

/-- The same authored rows supply the plans for every graph and vertex map. -/
def prepared : RuleProgram language.rewrites :=
  (compileProgram? language.rewrites).get (by decide +kernel)

def frontier {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (subject : Pattern) : List Pattern :=
  prepared.plans.flatMap (fun plan => plan.run (relationEnv source target hom) language subject)

theorem frontier_eq {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (subject : Pattern) :
    frontier source target hom subject = rewriteOnce source target hom subject := by
  unfold frontier rewriteOnce
  rw [prepared.run_eq_rootFrontier, rewriteAt_one_eq_rewriteStepWithPremisesUsing]

/-- Both directions hold for arbitrary raw terms, including malformed
walk encodings. The graph's authored guards still decide which can step. -/
theorem step_iff_mem_frontier {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (before after : Pattern) :
    (theory source target hom).Step before after ↔ after ∈ frontier source target hom before := by
  rw [frontier_eq, step_iff_mem_rewriteOnce]

private theorem prepared_of_path {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) :
    ∀ {before after : Pattern}, (theory source target hom).RewritePath before after →
      Relation.ReflTransGen (fun first last => last ∈ frontier source target hom first) before after
  | _, _, .nil _ => .refl
  | _, _, .cons edge tail =>
    (prepared_of_path source target hom tail).head
      ((step_iff_mem_frontier source target hom _ _).mp edge)

/-- A prepared path has exactly the authored finite-path semantics. -/
theorem path_iff {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (before after : Pattern) :
    Nonempty ((theory source target hom).RewritePath before after) ↔
      Relation.ReflTransGen (fun first last => last ∈ frontier source target hom first) before after := by
  constructor
  · rintro ⟨path⟩
    exact prepared_of_path source target hom path
  · intro executed
    induction executed using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨.nil _⟩
    | head edge _ ih =>
      obtain ⟨tail⟩ := ih
      exact ⟨.cons ((step_iff_mem_frontier source target hom _ _).mpr edge) tail⟩

theorem nativeWalk_iff_prepared {n m : Nat}
    (source : SimpleGraph (Fin n)) (target : SimpleGraph (Fin m))
    [DecidableRel source.Adj] [DecidableRel target.Adj]
    (hom : source →g target) (start finish : Fin n) (term : Pattern) :
    NativeWalk source target hom start finish term ↔
      grammarWalk term ∧ walkValueAt start finish term ∧
      ∃ last, Relation.ReflTransGen (fun first last => last ∈ frontier source target hom first)
        (.apply "ReverseRequest" [term]) last ∧ walkDoneAt finish start last := by
  rw [nativeWalk_iff]
  constructor
  · rintro ⟨grammar, indexed, last, path, terminal⟩
    exact ⟨grammar, indexed, last, (path_iff source target hom _ _).mp path, terminal⟩
  · rintro ⟨grammar, indexed, last, path, terminal⟩
    exact ⟨grammar, indexed, last, (path_iff source target hom _ _).mpr path, terminal⟩

end Mettapedia.GraphTheory.Walk.PreparedRules
