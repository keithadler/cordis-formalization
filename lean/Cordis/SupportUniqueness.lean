import Cordis.SupportOrder
import Cordis.SupportAtQuiescence
import Cordis.OrderingIntervals

/-! Lemma77 without the false Lemma75. Actual execution derives a rank on live
installed parent/provider edges. That rank proves Active is contained in every
solution of Equation62. Acyclic provider induction proves the opposite inclusion.
Registry finiteness is derived from the actual finite execution. -/
namespace Cordis.SupportUniqueness
open Calculus Stages SupportAtQuiescence SupportOrder
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]
set_option linter.unusedSectionVars false

def FiniteDomain (r : R) : Prop := ∃ names : List Name, ∀ name fiber, r name = some fiber → name ∈ names

theorem finite_of_origins {r s : R} (old : FiniteDomain r) (origins : WellFormed.DeclarationOrigins r s) :
    FiniteDomain s := by
  obtain ⟨names, covered⟩ := old
  refine ⟨names, ?_⟩
  intro name fiber present
  obtain ⟨before, found, _⟩ := origins name fiber present
  exact covered name before found

theorem modify_finite (r : R) (actor : Name) (change : F → F) (old : FiniteDomain r) :
    FiniteDomain (Calculus.modify r actor change) := by
  obtain ⟨names, covered⟩ := old
  refine ⟨names, ?_⟩
  intro name fiber present
  by_cases same : name = actor
  · subst name
    cases found : r actor with
    | none => simp [Calculus.modify, found] at present
    | some before => exact covered actor before found
  · exact covered name fiber (by simpa [Calculus.modify, same] using present)

theorem put_finite (r : R) (actor : Name) (fiber : F) (old : FiniteDomain r) :
    FiniteDomain (put r actor fiber) := by
  obtain ⟨names, covered⟩ := old
  refine ⟨actor :: names, ?_⟩
  intro name entry present
  by_cases same : name = actor
  · simp [same]
  · exact List.mem_cons_of_mem actor (covered name entry (by simpa [put, same] using present))

theorem land_finite (program : Code → Instruction Name Key Value Code Error)
    {r s : R} {actor : Name} {code : Code} {inverse : Inverse Name Key Value} {next : Option Code}
    (landed : Land program actor code r s inverse next) (old : FiniteDomain r) : FiniteDomain s := by
  cases landed with
  | unit => exact old
  | provide => exact modify_finite _ _ _ old
  | operate => exact modify_finite _ _ _ old
  | instantiate => exact put_finite _ _ _ old

theorem calculus_step_finite (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Calculus.Step (Land program) Stages.undo r s) (old : FiniteDomain r) : FiniteDomain s := by
  cases step with
  | insert => exact put_finite _ _ _ old
  | retire => exact modify_finite _ _ _ old
  | remove actor ready =>
    obtain ⟨names, covered⟩ := old
    refine ⟨names, ?_⟩
    intro name fiber present
    by_cases same : name = actor
    · simp [erase, same] at present
    · exact covered name fiber (by simpa [erase, same] using present)
  | begin => exact modify_finite _ _ _ old
  | iter _ _ _ _ _ _ _ _ _ _ _ landed | finish _ _ _ _ _ _ _ _ _ _ landed =>
    exact modify_finite _ _ _ (land_finite program landed old)
  | divert _ _ _ _ _ _ _ _ _ _ alternative =>
    rcases alternative with ⟨rfl, _⟩ | ⟨inverse, next, landed, _⟩
    · exact modify_finite _ _ _ old
    · exact modify_finite _ _ _ (land_finite program landed old)
  | leave => exact modify_finite _ _ _ old
  | unload actor fiber acc view present unloading free =>
    exact modify_finite _ _ _ (finite_of_origins old (Frame.discharge_origins r acc))

theorem step_finite (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Orchestration.Step program r s) (old : FiniteDomain r) : FiniteDomain s :=
  calculus_step_finite program step.toCalculus old

theorem reachable_finite (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : Orchestration.Run program (fun _ => none) r) : FiniteDomain r := by
  have preserves : ∀ {a b : R}, Orchestration.Run program a b → FiniteDomain a → FiniteDomain b := by
    intro a b path
    induction path with
    | refl => exact id
    | step _ move ih => intro old; exact step_finite program move (ih old)
  exact preserves run ⟨[], by intro n f impossible; cases impossible⟩

theorem reachable_disjoint (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : Orchestration.Run program (fun _ => none) r) : WellFormed.Disjoint r := by
  have preserves : ∀ {a b : R}, Orchestration.Run program a b → WellFormed.Disjoint a → WellFormed.Disjoint b := by
    intro a b path
    induction path with
    | refl => exact id
    | step _ move ih => intro old; exact WellFormed.step_disjoint program move.toCalculus (ih old)
  exact preserves run WellFormed.disjoint_empty

/-- A relation confined to active support edges, with the endpoint conditions
spelled out. It is strictly smaller than Definition74's unrestricted relation. -/
def ActivePredecessor (r : R) (predecessor name : Name) : Prop :=
  Active r name ∧ Active r predecessor ∧ ∃ fiber prior,
    r name = some fiber ∧ r predecessor = some prior ∧
    (fiber.parent = some predecessor ∨ ∃ key,
      fiber.component.requires key = true ∧ prior.component.provides key = true)

theorem active_edge_decreases (r : R) (rank : Name → Nat) (ordered : Ordered r rank)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (fixed : Solution r (Active r)) {predecessor name : Name} (edge : ActivePredecessor r predecessor name) :
    rank predecessor < rank name := by
  obtain ⟨⟨activeFiber, activeFound, available⟩, _, fiber, prior, found, priorFound, relationship⟩ := edge
  have same : activeFiber = fiber := Option.some.inj (activeFound.symm.trans found)
  subst activeFiber
  have committed : ∃ view, fiber.phase.committed = some view := by
    cases phase : fiber.phase <;> simp [phase, Phase.available] at available
    exact ⟨_, rfl⟩
  obtain ⟨view, committed⟩ := committed
  rcases relationship with parent | ⟨key, required, provided⟩
  · obtain ⟨entry, entryFound, live, _⟩ := (fixed name).mp ⟨fiber, found, available⟩
    have same : entry = fiber := Option.some.inj (entryFound.symm.trans found)
    subst entry
    exact ordered.parent name fiber predecessor view found parent live committed
  · have identifies := OrderingIntervals.declared_provider_is_committed r name predecessor fiber prior view key
      supported owned disjoint found priorFound committed required provided
    exact ordered.provider name predecessor key ⟨fiber, view, found, required, committed, identifies⟩

/-- A rank on installed demands and captured child edges orders the active
support relation whenever the active fibers satisfy its clauses. -/
private theorem active_wellFounded_of_rank {r : R} (ranked : Ranked r)
    (supported : Ordering.Supported r) (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (fixed : Solution r (Active r)) : WellFounded (ActivePredecessor r) := by
  obtain ⟨rank, _, _, ordered⟩ := ranked
  exact Subrelation.wf (fun {_ _} edge => active_edge_decreases r rank ordered
    supported owned disjoint fixed edge) (measure rank).wf

private theorem active_subset_of_wellFounded {r : R} (activeOrder : WellFounded (ActivePredecessor r))
    (fixed : Solution r (Active r))
    (set : Name → Prop) (solution : Solution r set) (name : Name) : Active r name → set name := by
  apply activeOrder.induction name
  intro name ih active
  obtain ⟨fiber, found, live, parent, providers⟩ := (fixed name).mp active
  apply (solution name).mpr
  refine ⟨fiber, found, live, ?_, ?_⟩
  · rcases parent with root | ⟨ancestor, ancestry, ancestorActive⟩
    · exact .inl root
    · obtain ⟨owner, ownerFound, ownerAvailable⟩ := ancestorActive
      exact .inr ⟨ancestor, ancestry, ih ancestor
        ⟨active, ⟨owner, ownerFound, ownerAvailable⟩, fiber, owner, found, ownerFound, .inl ancestry⟩
        ⟨owner, ownerFound, ownerAvailable⟩⟩
  · intro key required
    obtain ⟨provider, entry, providerFound, providerActive, provided⟩ := providers key required
    exact ⟨provider, entry, providerFound, ih provider
      ⟨active, providerActive, fiber, entry, found, providerFound, .inr ⟨key, required, provided⟩⟩ providerActive,
      provided⟩

/-- Eq. (63) uses invariants preserved by each selected structural step.
The step's original program is immaterial to these endpoint premises. -/
theorem support_unique_of_ranked {r : R} (finite : FiniteDomain r)
    (ranked : Ranked r) (captured : ChildProvenance.Captured r) (supported : Ordering.Supported r)
    (owned : Safety.Owned r) (disjoint : WellFormed.Disjoint r)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends r)) (quiet : Progress.Quiet r) (total : TotalProvision r) :
    Solution r (Active r) ∧ ∀ set : Name → Prop, Solution r set → ∀ name, set name ↔ Active r name := by
  obtain ⟨names, covered⟩ := finite
  have fixed := active_solution_of_capture captured quiet total
  have activeOrder := active_wellFounded_of_rank ranked supported owned disjoint fixed
  refine ⟨fixed, ?_⟩
  intro set solution name
  exact ⟨solution_subset_active r quiet total names covered acyclic set solution name,
    active_subset_of_wellFounded activeOrder fixed set solution name⟩

/-- Lemma77, including existence and uniqueness of the support set. All state
invariants and finite-domain premises follow from the real provenance-correct
execution; only the paper's acyclicity, quiet and total-provision hypotheses
remain. Lemma75 is not used. -/
theorem support_unique_active (program : Code → Instruction Name Key Value Code Error)
    {r : R} (run : Orchestration.Run program (fun _ => none) r)
    (acyclic : FiniteOrder.Acyclic (Progress.Depends r))
    (quiet : Progress.Quiet r) (total : TotalProvision r) :
    Solution r (Active r) ∧ ∀ set : Name → Prop, Solution r set → ∀ name, set name ↔ Active r name :=
  support_unique_of_ranked (reachable_finite program run) (reachable_ranked program run)
    (ChildProvenance.reachable_captured program run) run.reachable_invariants.2.2.1
    run.reachable_invariants.2.1 (reachable_disjoint program run) acyclic quiet total

end Cordis.SupportUniqueness
