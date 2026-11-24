import Cordis.Repairs.CompatibleProvision
import Cordis.Results.GlobalProvisionContradiction

/-! The same nonempty provision that the global interpretation forbids is
admitted by the repaired, component-compatible semantics. This is a positive
witness and exact recovery example, not merely exclusion of a counterexample.
-/
namespace Cordis.Repairs.ProvisionExample
open TypedRegistry
open TypedRegistry.GlobalProvisionContradiction
open CompatibleProvision

def input : Gamma operations 0 providerComponent :=
  ⟨providerInput,
    step_allowed provider_begin (step_allowed provider_insert empty_allowed),
    ⟨{ (fresh providerComponent none : Row) with phase := .reloading true [] view }, rfl, rfl⟩⟩

def output : Gamma operations 0 providerComponent := setSlot () rfl (some ()) input

def observation (_ : Unit) : Setoid Unit := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem succeeds : (provision () rfl ()).run input = some (output, restrict () rfl, PUnit.unit) := rfl

theorem installs_binding : tableAt output.val 0 () = some () := rfl

theorem restores_input : restrict () rfl output = some input :=
  provision_exact_recovery () rfl () input output _ _ succeeds

theorem actual_output : output.val = providerOutput := rfl

theorem witnessed : PartialInverseObservation.Witnessed (provision (ops := operations)
    (actor := 0) (component := providerComponent) () rfl ())
    (Observed observation (fun _ => True)) :=
  provision_witnessed observation (fun _ => True) () trivial rfl ()

theorem iterator_witnessed : PartialIterators.Witnessed (Observed observation (fun _ => True))
    (terminal (ops := operations) (actor := 0) (component := providerComponent) () rfl ()) :=
  terminal_witnessed observation (fun _ => True) () trivial rfl ()

theorem unit_probe_excluded : ¬ Compatible operations 0 providerComponent unitInput := by
  rintro ⟨_, fiber, found, same⟩
  have row : fresh unitComponent none = fiber := Option.some.inj found
  subst fiber
  have impossible := congrArg (fun c : Calculus.Component Unit Bool => c.provides ()) same
  cases impossible

/-- Partiality alone is insufficient if the old global comparison is kept:
the two table-equivalent inputs must still agree in definedness. -/
theorem partiality_alone_fails (forward : State → Option State)
    (success : ∃ result, forward providerInput = some result)
    (rejects : forward unitInput = none) :
    ¬ PartialInverseObservation.MapRelated
      (TypedStateObservation.TablesRelatedAt observation (fun _ => True)) forward forward := by
  intro respects
  have related := respects providerInput unitInput (inputs_related observation)
  obtain ⟨result, success⟩ := success
  simp [success, rejects, Iterators.OptionRel] at related

end Cordis.Repairs.ProvisionExample
