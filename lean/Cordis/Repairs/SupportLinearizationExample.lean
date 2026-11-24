import Cordis.Repairs.SupportLinearization
import Cordis.Repairs.OperationExample

/-! A typed, provision-producing quiescent trace. The support enumeration
orders the real provider before the consumer that modifies its binding. -/
namespace Cordis.Repairs.SupportLinearizationExample
open TypedRegistry OperationExample SupportLinearization

def completed : State := mark output.val 1 (.active [.operate 0 () predecessor] view)

theorem finish_consumer : Step program .finish 1 ready completed :=
  .finish ready output.val 1 { (fresh consumer none : Row) with phase := .reloading false [] view }
    false [] view (.operate 0 () predecessor) rfl rfl
    ⟨rfl, fun key _ => ⟨trivial, by cases key; decide⟩⟩ native_landing

def states : Nat → State
  | 0 => empty
  | 1 => inserted
  | 2 => begun
  | 3 => active
  | 4 => joined
  | 5 => ready
  | _ => completed

def rules : Nat → Labeled.Rule
  | 0 | 3 => .insert
  | 1 | 4 => .begin
  | _ => .finish

def actors (t : Nat) : Nat := if t < 3 then 0 else 1

def trace : Trace program empty 6 where
  state := states
  rule := rules
  actor := actors
  start := rfl
  step t bounded := by
    have cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact insert_provider
    · exact begin_provider
    · exact finish_provider
    · exact insert_consumer
    · exact begin_consumer
    · exact finish_consumer

theorem roots : trace.RootInsertions := by
  intro t bounded label
  have cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fresh provider none, rfl, rfl⟩
  · cases label
  · cases label
  · exact ⟨fresh consumer none, rfl, rfl⟩
  · cases label
  · cases label

def providerRow : Row :=
  { (fresh provider none : Row) with table := fun _ => some 11
                                     phase := .active [.restrict 0 ()] view }

def consumerRow : Row :=
  { (fresh consumer none : Row) with phase := .active [.operate 0 () predecessor] view }

theorem endpoint_rows (name : Nat) : completed name =
    if name = 0 then some providerRow else if name = 1 then some consumerRow else none := by
  by_cases providerName : name = 0
  · subst name
    rfl
  by_cases consumerName : name = 1
  · subst name
    rfl
  simp [completed, BoundOperation.setSlot_value, input, output, ready, joined, active, supplied,
    begun, inserted, empty, mark, write, TypedRegistry.modify, put, providerName, consumerName]

theorem endpoint_quiet : Quiet completed := by
  intro name row found
  rw [endpoint_rows] at found
  by_cases providerName : name = 0
  · subst name
    have same := Option.some.inj found
    subst row
    exact ⟨rfl, fun _ impossible => Bool.noConfusion impossible⟩
  by_cases consumerName : name = 1
  · subst name
    change some consumerRow = some row at found
    have same := Option.some.inj found
    subst row
    exact ⟨rfl, fun key _ => ⟨trivial, by cases key; decide⟩⟩
  simp [providerName, consumerName] at found

theorem endpoint_total : TotalProvision completed := by
  intro name row found _ key
  rw [endpoint_rows] at found
  by_cases providerName : name = 0
  · subst name
    have same := Option.some.inj found
    subst row
    simp [providerRow, fresh, provider]
  by_cases consumerName : name = 1
  · subst name
    change some consumerRow = some row at found
    have same := Option.some.inj found
    subst row
    simp [consumerRow, fresh, consumer]
  simp [providerName, consumerName] at found

theorem only_precedence {prior name : Nat} (edge : precedes completed prior name) :
    prior = 0 ∧ name = 1 := by
  obtain ⟨key, ⟨provided, foundProvider, providedKey⟩, ⟨required, foundConsumer, requiredKey⟩⟩ := edge
  rw [endpoint_rows] at foundProvider foundConsumer
  have first : prior = 0 := by
    by_cases atProvider : prior = 0
    · exact atProvider
    by_cases atConsumer : prior = 1
    · simp [atConsumer] at foundProvider
      subst provided
      cases providedKey
    · simp [atProvider, atConsumer] at foundProvider
  have second : name = 1 := by
    by_cases atConsumer : name = 1
    · exact atConsumer
    by_cases atProvider : name = 0
    · simp [atProvider] at foundConsumer
      subst required
      cases requiredKey
    · simp [atConsumer, atProvider] at foundConsumer
  exact ⟨first, second⟩

theorem acyclic : FiniteOrder.Acyclic (precedes completed) := by
  intro name cycle
  have rank {first last : Nat} (path : FiniteOrder.Chain (precedes completed) first last) : first < last := by
    induction path with
    | single edge => obtain ⟨rfl, rfl⟩ := only_precedence edge; decide
    | tail _ edge prior => obtain ⟨rfl, rfl⟩ := only_precedence edge; omega
  exact (Nat.lt_irrefl _ (rank cycle))

/-- The amended support result admits a real binding. Its unique active
support enumeration places provider 0 before consumer 1. -/
theorem nonempty_support :
    tableAt completed 0 () = some 11 ∧
    WellFounded (ConsultedSupport completed) ∧
    SupportSolution completed (Active completed) ∧
    (∀ set, SupportSolution completed set → set = Active completed) ∧
    ∃ order, Linearization (Active completed) (ActiveSupport completed) order ∧ [0, 1].Sublist order := by
  have support := typed_support_consultations trace roots acyclic
  have fixed := lemma77_typed trace roots acyclic endpoint_quiet endpoint_total
  obtain ⟨order, plan⟩ := typed_active_linearization trace roots endpoint_quiet endpoint_total
  refine ⟨rfl, support.1, fixed.1, fixed.2, order, plan, plan.ordered 0 1 (.single ?_)⟩
  refine ⟨⟨providerRow, rfl, trivial⟩, ⟨consumerRow, rfl, trivial⟩, rfl, rfl, .inl ?_⟩
  exact ⟨(), ⟨providerRow, rfl, rfl⟩, ⟨consumerRow, rfl, rfl⟩⟩

end Cordis.Repairs.SupportLinearizationExample
