import Cordis.Results.TypedGlobalSupport

/-!
An explicit two-input contradiction for the GLOBAL reading of Definitions
37, 48, 49, 51, 55 and 56 (PDF pp. 25, 31-33, 38-39).

There is one key k with a unit value. Both inputs contain exactly one fiber n
and have empty tables. In `providerInput`, n declares p={k} and is about to
provision k. In `unitInput`, n is a fresh unit component declaring p=empty.
Definition 51 cannot distinguish the inputs, even at S={k}.

Suppose the provider's head is a witnessed iterator on one Gamma containing
BOTH inputs, its forward map is globally confined to n, and every output in
Gamma obeys the table-ownership invariant dom(sigma_n) subset p_n (p. 33).
The actual provision produces a binding on the first input. On the second,
confinement cannot add a fiber or alter n's declaration, so ownership forces
every output table to remain empty. Its two outputs are distinguishable by
the presence test at k, contradicting the witness's forward respect.

This is deliberately a conditional semantic impossibility, not a claim that
every interpretation of the paper is inconsistent. Restricting a head's domain
to states with its actor's fixed component excludes `unitInput` and defeats
this argument. Such a repair must be stated and propagated to the replay
lemmas; this file does not prove those repaired lemmas.
-/
namespace Cordis.TypedRegistry.GlobalProvisionContradiction

open PaperEffectEquations (CoeffectOperations)
open TypedStateObservation (Semantics TablesRelatedAt observation)

abbrev Values : Unit → Type := fun _ => Unit
abbrev State := Registry Nat Values Bool
abbrev Row := Fiber Nat Values Bool

def operations : CoeffectOperations Values where
  Name _ := Empty
  Argument _ op := nomatch op
  Outcome _ op := nomatch op
  operation _ op := nomatch op

def program (code : Bool) : Instruction Nat operations Bool :=
  ⟨if code then .provide () () else .unit, fun _ => none⟩
def providerComponent : Calculus.Component Unit Bool := ⟨fun _ => false, fun _ => true, true⟩
def unitComponent : Calculus.Component Unit Bool := ⟨fun _ => false, fun _ => false, false⟩
def empty : State := fun _ => none
def view : Calculus.View Nat Unit := fun _ => 0
def providerInserted : State := put empty 0 (fresh providerComponent none)
def providerInput : State := mark providerInserted 0 (.reloading true [] view)
def unitInput : State := put empty 0 (fresh unitComponent none)
def providerOutput : State := write providerInput 0 () (some ())

/-- The displayed primitive genuinely lands at the proposed source, with
the paper's restriction inverse. The global witness is what is impossible. -/
theorem provision_lands : Land program 0 true providerInput providerOutput (.restrict 0 ()) none :=
  .provide providerInput 0 true
    { (fresh providerComponent none : Row) with phase := .reloading true [] view }
    () () rfl rfl rfl rfl

theorem provider_insert : Step program .insert 0 empty providerInserted :=
  .insert empty 0 providerComponent none ⟨rfl, by simp, fun _ _ => trivial⟩

theorem provider_begin : Step program .begin 0 providerInserted providerInput :=
  .begin providerInserted 0 (fresh providerComponent none) view rfl rfl
    ⟨rfl, fun _ required => Bool.noConfusion required⟩

theorem unit_insert : Step program .insert 0 empty unitInput :=
  .insert empty 0 unitComponent none ⟨rfl, by simp, fun _ _ => trivial⟩

theorem unit_witnessed (sem : Semantics Nat Values Bool) (keys : Unit → Prop) :
    @Iterators.WitnessedIterator _ (observation operations sem keys) (Iterators.embed Effects.identity) :=
  @Iterators.witnessed_embed _ (observation operations sem keys) Effects.identity
    (@Effects.witnessed_identity _ (observation operations sem keys))

theorem provider_tables_empty : EmptyTables providerInput := by
  intro name key
  by_cases same : name = 0 <;>
    simp [providerInput, providerInserted, empty, tableAt, mark, modify, put, fresh, same]

theorem unit_tables_empty : EmptyTables unitInput := by
  intro name key
  simp [unitInput, empty, tableAt, put, fresh]

theorem inputs_related (observe : ∀ key, Setoid (Values key)) :
    TablesRelatedAt observe (fun _ => True) providerInput unitInput := by
  intro key _
  constructor
  · intro owner value found
    rw [provider_tables_empty owner key] at found
    cases found
  · intro owner value found
    rw [unit_tables_empty owner key] at found
    cases found

/-- The assumptions are separated to expose exactly what must change in a
charitable reading: the shared domain, confinement on that domain, ownership
of its outputs, the claimed concrete provision, or global witness respect. -/
theorem no_global_provision
    (sem : Semantics Nat Values Bool)
    (providerAdmitted : sem.domain providerInput)
    (unitAdmitted : sem.domain unitInput)
    (owned : ∀ (input : sem.Gamma) name fiber, input.val name = some fiber →
      ∀ key, fiber.table key ≠ none → fiber.component.provides key = true)
    (head : Iterators.Iterator sem.Gamma)
    (actual : (Tracking.forward head.effect ⟨providerInput, providerAdmitted⟩).val = providerOutput)
    (confined : ProvisionFrame sem 0 (Tracking.forward head.effect))
    (witness : @Iterators.WitnessedIterator _ (observation operations sem (fun _ => True)) head) : False := by
  letI : Setoid sem.Gamma := observation operations sem (fun _ => True)
  let provider : sem.Gamma := ⟨providerInput, providerAdmitted⟩
  let probe : sem.Gamma := ⟨unitInput, unitAdmitted⟩
  let forward := Tracking.forward head.effect
  have related : (observation operations sem (fun _ => True)).r provider probe :=
    inputs_related sem.keyObservation
  have outputs : TablesRelatedAt sem.keyObservation (fun _ => True)
      (forward provider).val (forward probe).val := witness.effect_witnessed.forward_respects related
  have bound : tableAt (forward provider).val 0 () = some () := by
    change tableAt (Tracking.forward head.effect ⟨providerInput, providerAdmitted⟩).val 0 () = some ()
    rw [actual]
    rfl
  obtain ⟨owner, value, found, _⟩ := (outputs () trivial).1 0 () bound
  have probeAt : probe.val 0 = some (fresh unitComponent none) := rfl
  obtain ⟨noNewNames, sameComponent⟩ := confined probe (fresh unitComponent none) probeAt
  by_cases same : owner = 0
  · subst owner
    cases entry : (forward probe).val 0 with
    | none => simp [tableAt, entry] at found
    | some fiber =>
      have binding : fiber.table () = some value := by simpa [tableAt, entry] using found
      have declared := owned (forward probe) 0 fiber entry () (by rw [binding]; simp)
      have stable := sameComponent fiber entry
      rw [stable] at declared
      cases declared
  · have missing := noNewNames owner (by simp [probe, unitInput, put, empty, same])
    change (forward probe).val owner = none at missing
    simp [tableAt, missing] at found

end Cordis.TypedRegistry.GlobalProvisionContradiction
