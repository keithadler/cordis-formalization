import Cordis.TranspositionTables
import Cordis.StageSimulation
import Cordis.TranspositionCallbacks

/-! The operation/operation primitive row of Lemma78(1). Distinct coordinates
retain literal input values. A shared coordinate uses only the value-level
coeffect contract to derive successful swapped callbacks, literal outcomes,
observed final values, and cross-captured inverse congruence. -/
namespace Cordis.Transposition
open Calculus Stages Labeled StageRecovery AccumulatorProvenance Independence Effects
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

theorem location_of_route_table (r : R) (actor owner : Name) (key : Key) (value : Value)
    (route : GuardedApplications.routing r actor key = some owner) (bound : tableAt r owner key = some value) :
    location r actor key = some (owner, value) := by
  simp [GuardedApplications.location_routing, route, bound]

theorem table_of_location (r : R) (actor owner : Name) (key : Key) (value : Value)
    (located : location r actor key = some (owner, value)) : tableAt r owner key = some value := by
  obtain ⟨fiber, present, bound⟩ := Safety.location_binding r actor owner key value located
  simpa [tableAt, present] using bound

theorem tableAt_write_here (r : R) (owner : Name) (key : Key) (value : Option Value) (present : r owner ≠ none) :
    tableAt (write r owner key value) owner key = value := by
  cases found : r owner with
  | none => exact False.elim (present found)
  | some fiber => simp [tableAt, write, Calculus.modify, found]

theorem location_write_away (r : R) (actor owner selected : Name) (key query : Key) (value : Option Value)
    (route : GuardedApplications.routing r actor query = some selected)
    (different : selected ≠ owner ∨ query ≠ key) :
    location (write r owner key value) actor query = location r actor query := by
  rw [GuardedApplications.location_routing, GuardedApplications.location_routing, write_routing, route]
  change (tableAt (write r owner key value) selected query).map (fun v => (selected, v)) =
    (tableAt r selected query).map (fun v => (selected, v))
  rw [tableAt_write_away r owner selected key query value different]

section Observation
variable [Setoid Value]

/-- Both actual primitive instructions are replayed constructively. The output
contains their unchanged outcome-selected continuations, the final table
diamond, and the semantic relation for each actual captured inverse. -/
theorem operations_landing_diamond (program : Code → Instruction Name Key Value Code Error)
    (r : R) (first second owner other : Name) (key query : Key) (firstCode secondCode : Code)
    (firstRun secondRun : Value → Except Error (Value × (Value → Value) × Value))
    (firstAction : (program firstCode).action = .operate key firstRun)
    (secondAction : (program secondCode).action = .operate query secondRun)
    (independent : key = query → CallbackExchange firstRun secondRun)
    (before after secondBefore final : Value) (firstInverse secondInverse : Value → Value)
    (firstOutcome secondOutcome : Value)
    (firstLocated : location r first key = some (owner, before))
    (firstCalled : firstRun before = .ok (after, firstInverse, firstOutcome))
    (secondLocated : location (write r owner key (some after)) second query = some (other, secondBefore))
    (secondCalled : secondRun secondBefore = .ok (final, secondInverse, secondOutcome))
    (firstRespects : Effects.Respects firstInverse) (secondRespects : Effects.Respects secondInverse) :
    ∃ middle swapped firstUndo secondUndo,
      Land program second secondCode r middle secondUndo ((program secondCode).next (.value secondOutcome)) ∧
      Land program first firstCode middle swapped firstUndo ((program firstCode).next (.value firstOutcome)) ∧
      TablesRelated swapped (write (write r owner key (some after)) other query (some final)) ∧
      StageSimulation.InverseRelated secondUndo (.operate other query secondInverse) ∧
      StageSimulation.InverseRelated firstUndo (.operate owner key firstInverse) := by
  have firstRoute : GuardedApplications.routing r first key = some owner := Stages.location_owner firstLocated
  have secondRoute : GuardedApplications.routing (write r owner key (some after)) second query = some other :=
    Stages.location_owner secondLocated
  rw [write_routing] at secondRoute
  have ownerPresent := location_owner_present r first owner key before firstLocated
  by_cases same : (owner, key) = (other, query)
  · have owners : owner = other := congrArg Prod.fst same
    have keys : key = query := congrArg Prod.snd same
    subst other query
    have afterLocated : location (write r owner key (some after)) second key = some (owner, after) :=
      location_of_route_table _ second owner key after
        (by simpa only [write_routing] using secondRoute) (tableAt_write_here r owner key _ ownerPresent)
    have values : after = secondBefore := congrArg Prod.snd (Option.some.inj (afterLocated.symm.trans secondLocated))
    subst secondBefore
    obtain ⟨afterSecond, secondBeforeInverse, finalSwapped, firstAfterInverse,
      secondBeforeCalled, firstAfterCalled, finalRelated, secondInverses, firstInverses⟩ :=
      (independent rfl) before after final firstInverse secondInverse
        firstOutcome secondOutcome firstCalled secondCalled
    have secondBeforeLocated := location_of_route_table r second owner key before secondRoute
      (table_of_location r first owner key before firstLocated)
    have firstAfterLocated := location_of_route_table (write r owner key (some afterSecond)) first owner key afterSecond
      (by simpa only [write_routing] using firstRoute) (tableAt_write_here r owner key _ ownerPresent)
    refine ⟨write r owner key (some afterSecond), write (write r owner key (some afterSecond)) owner key (some finalSwapped),
      .operate owner key firstAfterInverse, .operate owner key secondBeforeInverse,
      .operate r second secondCode key secondRun owner before afterSecond secondBeforeInverse secondOutcome
        secondAction secondBeforeLocated secondBeforeCalled,
      .operate _ first firstCode key firstRun owner afterSecond finalSwapped firstAfterInverse firstOutcome
        firstAction firstAfterLocated firstAfterCalled, ?_, ?_, ?_⟩
    · rw [write_twice, write_twice]
      intro name atKey
      by_cases sameOwner : name = owner
      · subst name
        by_cases sameKey : atKey = key
        · subst atKey
          rw [tableAt_write_here _ _ _ _ ownerPresent, tableAt_write_here _ _ _ _ ownerPresent]
          exact finalRelated
        · cases present : r owner <;> simpa [tableAt, write, Calculus.modify, sameKey, present] using tables_refl r owner atKey
      · simpa [tableAt, write, Calculus.modify, sameOwner] using tables_refl r name atKey
    · exact .operate owner key (Independence.related_symm secondInverses)
    · exact .operate owner key firstInverses
  · have secondAway : other ≠ owner ∨ query ≠ key := by
      by_cases owners : other = owner
      · right
        intro keys
        exact same (by simp [owners, keys])
      · exact .inl owners
    have firstAway : owner ≠ other ∨ key ≠ query := by
      rcases secondAway with owners | keys
      · exact .inl (Ne.symm owners)
      · exact .inr (Ne.symm keys)
    have secondBeforeLocated : location r second query = some (other, secondBefore) :=
      (location_write_away r second owner other key query (some after) secondRoute secondAway).symm.trans secondLocated
    have firstAfterLocated : location (write r other query (some final)) first key = some (owner, before) :=
      (location_write_away r first other owner query key (some final) firstRoute firstAway).trans firstLocated
    refine ⟨write r other query (some final), write (write r other query (some final)) owner key (some after),
      .operate owner key firstInverse, .operate other query secondInverse,
      .operate r second secondCode query secondRun other secondBefore final secondInverse secondOutcome
        secondAction secondBeforeLocated secondCalled,
      .operate _ first firstCode key firstRun owner before after firstInverse firstOutcome
        firstAction firstAfterLocated firstCalled, ?_, ?_, ?_⟩
    · rw [writes_commute r other owner query key (some final) (some after) secondAway]
      exact tables_refl _
    · exact .operate other query secondRespects
    · exact .operate owner key firstRespects

end Observation
end Cordis.Transposition
