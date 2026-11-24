import Cordis.RuleEvaluation
import Cordis.PaperStateObservation
import Cordis.SupportAtQuiescence

/-! The indexed equations in §4.3, pp. 39–52. The frozen iterator and
accumulator maps of Definition 58 are semantic parameters. -/
namespace Cordis.PaperTraceEquations
open Calculus Stages
universe u

/-- Eq. (53), including the concrete edit computed at the source step. -/
def Factors {Γ : Type u} (states : Nat → Γ) (psi edit : Nat → Γ → Γ) (t : Nat) : Prop :=
  states (t + 1) = edit t (psi t (states t))

/-- Eq. (54), with two admitted inputs. Field comparison uses the original
all-key union-table base for function and iterator types. -/
def StateEquivalent {Name Key Value Code Error : Type u}
    [DecidableEq Name] [DecidableEq Key]
    (sem : PaperStateObservation.Semantics Name Key Value Code Error)
    (left right : sem.Gamma) : Prop :=
  PaperStateObservation.Related sem left.val right.val

/-- Eq. (59), with provider first. -/
def Precedes {Name Key : Type u} (provides requires : Name → Key → Prop)
    (provider consumer : Name) : Prop :=
  ∃ key, provides provider key ∧ requires consumer key

/-- Eq. (61), on the registry domain. The root marker uses none. -/
def SupportEdge {Name : Type u} (registered : Name → Prop) (precedes : Name → Name → Prop)
    (parent : Name → Option Name) (m n : Name) : Prop :=
  registered m ∧ registered n ∧ (precedes m n ∨ parent n = some m)

/-- Eq. (62). Here the modeled registry supplies d, p, π, and τ. -/
abbrev SupportSolution := @SupportAtQuiescence.Solution

/-- Lemma 77, Eq. (63). Its theorem premises include acyclic precedence,
a reachable quiescent registry, and total provision. -/
def SupportEquality {Name Key Value Code Error : Type u}
    (registry : Registry Name Key Value Code (Inverse Name Key Value) Error)
    (support : Name → Prop) : Prop :=
  support = SupportAtQuiescence.Active registry

end Cordis.PaperTraceEquations
