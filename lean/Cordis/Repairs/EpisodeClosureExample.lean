import Cordis.Repairs.EpisodeClosure
import Cordis.Repairs.IncarnationExample

/-! A reachable suffix enabled by an unguarded retirement of a replacement. -/
namespace Cordis.Repairs.EpisodeClosureExample
open Calculus Stages CommandBarrier IncarnationExample

def staleEpisode : EpisodeDependencies.ClosedEpisode staleClosingTrace where
  name := 0
  opened := 2
  closed := 8
  interval := by
    refine ⟨by decide, by decide, by decide, ?_, rfl, rfl⟩
    intro time first last
    have range : time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 ∨ time = 7 ∨ time = 8 := by omega
    rcases range with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change some view ≠ none <;> simp

/-- A native suffix can remove the reissued root only because the stale
retirement touched it. The incarnation-aware closing state keeps that
root live and unretired, so the same removal command is disabled. -/
theorem stale_closing_breaks_remove_suffix :
    OrchestrationSorting.Command.Step (.remove 1) (staleClosingTrace.state 9) (staleClosingTrace.state 10) ∧
    (EpisodeClosure.correctedClosure staleClosingTrace staleEpisode 1).map Fiber.retired = some false ∧
    EpisodeRollback.withdraws staleClosingTrace staleEpisode 8 1 = false ∧
    ¬ (OrchestrationSorting.Command.remove 1 : OrchestrationSorting.Command Nat Unit Bool).Enabled
      (EpisodeClosure.correctedClosure staleClosingTrace staleEpisode) := by
  refine ⟨⟨remove_reissued_root, rfl⟩, rfl, rfl, ?_⟩
  intro enabled
  have inactive : EpisodeClosure.correctedClosure staleClosingTrace staleEpisode 1 =
      some (fresh providerComponent none) := rfl
  change Removable (EpisodeClosure.correctedClosure staleClosingTrace staleEpisode) 1 at enabled
  rw [Removable, inactive] at enabled
  exact Bool.noConfusion enabled.1

end Cordis.Repairs.EpisodeClosureExample
