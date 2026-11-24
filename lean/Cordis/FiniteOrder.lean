import Cordis.Progress
import Init.Data.List.Nat.Basic

/-! Finite acyclic relations are well founded, with no pre-supplied ranking.
The rank counts reachable predecessors in a finite covering list. -/
namespace Cordis.FiniteOrder
universe u
variable {α : Type u}

inductive Chain (rel : α → α → Prop) : α → α → Prop where
  | single {a b} : rel a b → Chain rel a b
  | tail {a b c} : Chain rel a b → rel b c → Chain rel a c

def Acyclic (rel : α → α → Prop) : Prop := ∀ name, ¬ Chain rel name name

/-- Finite coverage is needed only for the first endpoint of an edge. The list
may contain duplicates and isolated nodes; neither changes the conclusion. -/
theorem wellFounded_of_finite_acyclic (rel : α → α → Prop) (nodes : List α)
    (covered : ∀ a b, rel a b → a ∈ nodes) (acyclic : Acyclic rel) : WellFounded rel := by
  classical
  let rank (a : α) := (nodes.filter (fun b => decide (Chain rel b a))).length
  have decreases : ∀ a b, rel a b → rank a < rank b := by
    intro a b edge
    have double : (nodes.filter (fun n => decide (Chain rel n b))).filter
        (fun n => decide (Chain rel n a)) = nodes.filter (fun n => decide (Chain rel n a)) := by
      rw [List.filter_filter]
      congr 1
      funext n
      by_cases before : Chain rel n a
      · have after : Chain rel n b := .tail before edge
        simp [before, after]
      · simp [before]
    have strict : ((nodes.filter (fun n => decide (Chain rel n b))).filter
        (fun n => decide (Chain rel n a))).length < (nodes.filter (fun n => decide (Chain rel n b))).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      refine ⟨a, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨covered a b edge, by simp [Chain.single edge]⟩
      · simpa using acyclic a
    simpa [double, rank] using strict
  exact Subrelation.wf (fun {a b} edge => decreases a b edge) (measure rank).wf

open Calculus Stages Ordering Progress
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

variable [DecidableEq Name] [DecidableEq Key]

end Cordis.FiniteOrder
