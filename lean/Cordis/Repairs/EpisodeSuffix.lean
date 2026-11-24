import Cordis.Repairs.EpisodeClosure
import Cordis.Repairs.EpisodeInterior
import Cordis.Repairs.GuardedSuffixTransport

/-! The interior replay supplies the actual closing cut and annotated word
for the guarded suffix. The suffix premise is an execution from the
incarnation-aware closing state. -/
namespace Cordis.Repairs.EpisodeSuffix
open Calculus Stages Indexed EpisodeDependencies EpisodeAnnotations EpisodeInterior EpisodeClosure
open PaperEffectEquations (CoeffectOperations ValueOperationWitness)
open PartialCoeffectIndependenceContracts (tableSetoid)
open TypedRegistry (encodeProgram RawRegistry Scalar)
open LegalHistory (Event RootExec eventRoots)
open Vestigial (CutNotes cutNotes recordSuffix)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
variable {program : Code → TypedRegistry.Instruction Name ops Code} {last : Nat}
local notation "A" => Scalar ops
local notation "R" => RawRegistry Name ops Code
local notation "Ev" => Event Name Key Code
local notation "Notes" => CutNotes Name Key A

/-- The finite interior replay can continue through a legal guarded suffix.
Only the selected vestiges are erased, and the original command payloads,
root order, and capture stamps are retained in both segments. -/
theorem replay_through_guarded_suffix
    (trace : Trace (encodeProgram program) (fun _ => none : R) last) (episode : ClosedEpisode trace)
    (rootInsertions : PaperLifecycleClaims.RootInsertions trace)
    (maximal : ∀ later : ClosedEpisode trace, ¬ EpisodeEdge episode later)
    (quiet : Progress.Quiet (trace.state last))
    (observe : ∀ key, Setoid (V key)) (recovery : ValueOperationWitness ops)
    (commutative : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {suffixEvents : List (Nat × Ev)} {final : R} {finalNotes : Notes}
    {suffixRoots : List (OrchestrationSorting.Command Name Key Code)}
    (suffix : GuardedSuffix.Exec (encodeProgram program) suffixEvents (correctedClosure trace episode)
      (postNotes trace episode) final finalNotes suffixRoots) :
    let cuts := List.range' episode.opened (episode.closed - episode.opened)
    let kept := cuts.filter (EpisodeSelection.keeps trace episode.name episode.opened episode.closed)
    letI : Setoid A := TypedCoeffectReplay.setoid observe
    ∃ (events : Nat → Ev) (interior : Trace (encodeProgram program) (trace.state (episode.opened - 1)) kept.length)
      (withdrawn : List Name) (after : R) (afterNotes : Notes),
      (∀ time, time < last → SourceEvent trace time (events time)) ∧
      (∀ index old, kept[index]? = some old → interior.rule index = trace.rule old ∧
        interior.actor index = trace.actor old ∧
        (events old).Step (encodeProgram program) (interior.state index) (interior.state (index + 1))) ∧
      RootExec (encodeProgram program) (kept.map events) (trace.state (episode.opened - 1))
        (interior.state kept.length) (cuts.flatMap fun time => eventRoots (trace.state time) (events time)) ∧
      withdrawn.Nodup ∧ (∀ name, name ∈ withdrawn ↔ EpisodeRollback.withdraws trace episode episode.closed name = true) ∧
      GuardedSuffix.Exec (encodeProgram program) (GuardedSuffix.pruneAll withdrawn suffixEvents)
        (interior.state kept.length)
        (recordSuffix interior.state interior.actor 0 kept (cutNotes trace.state trace.actor (episode.opened - 1)))
        after afterNotes suffixRoots ∧
      StageSimulation.Related Eq (Vestigial.eraseAll (GuardedSuffix.stillPresent withdrawn suffixEvents) final) after ∧
      NotesRelated (GuardedSuffix.eraseAllNotes (GuardedSuffix.stillPresent withdrawn suffixEvents) finalNotes) afterNotes := by
  letI : Setoid A := TypedCoeffectReplay.setoid observe
  obtain ⟨events, closing, actual, interiorRun, compared, indexed, reaches, labels, recorded, projects⟩ :=
    replay_interior_from_opening trace episode maximal quiet observe recovery commutative respect rootInsertions
  obtain ⟨names, distinct, selected, pruned⟩ :=
    guarded_suffix_from_closing_probe trace episode rootInsertions maximal quiet suffix
  obtain ⟨after, notes, transported, endpoint, paired, _⟩ :=
    GuardedSuffix.transport_exec observe program respect pruned (compared.symm (fun _ _ same => same.symm))
      recorded.symm projects
  rw [← reaches] at interiorRun transported
  exact ⟨events, indexed, names, after, notes, actual, labels, interiorRun, distinct, selected, transported, endpoint, paired⟩

end Cordis.Repairs.EpisodeSuffix
