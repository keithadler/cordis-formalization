import Cordis.Repairs.GuardedPartialApplications

/-! An actor provisions a real binding and then operates on it. At
unload the partial operation inverse must run before the restriction.
The recorded inverse has a genuine failure input outside this replay. -/
namespace Cordis.Repairs.ReplayBindingExample
open Calculus Stages StageRecovery LegalHistory GuardedHistory IncarnationReplay
open ReplayBindingDomains GuardedPartialApplications
open Vestigial (cutNotes eventActor)
open Iterators (OptionRel)

abbrev I := Inverse Unit Unit Nat
abbrev R := Registry Unit Unit Nat Bool I Unit
abbrev F := Fiber Unit Unit Nat Bool I Unit

def flip (value : Nat) : Nat := if value = 0 then 1 else 0
def inverseMap (inverse : Nat → Nat) (value : Nat) : Option Nat :=
  if value ≤ 1 then some (inverse value) else none

def callback (value : Nat) : Except Unit (Nat × (Nat → Nat) × Nat) :=
  if value ≤ 1 then .ok (flip value, flip, 0) else .error ()

def program (code : Bool) : Instruction Unit Unit Nat Bool Unit :=
  if code then ⟨.provide () 0, fun _ => some false⟩ else ⟨.operate () callback, fun _ => none⟩

private def observation : Setoid Nat := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

private theorem actual_action {code : Bool} {key : Unit} {call}
    (action : (program code).action = .operate key call) : call = callback := by
  cases code
  · exact (Action.operate.inj action).2.symm
  · cases action

def meaning : PartialReplayRegistry.Coeffects program where
  denote := fun _ => inverseMap
  agrees := by
    intro key inverse input output applied
    by_cases inDomain : input ≤ 1
    · exact Option.some.inj (by simpa [inverseMap, inDomain] using applied)
    · simp [inverseMap, inDomain] at applied
  admitted := fun _ map => map = inverseMap flip
  observe := fun _ => observation
  laws := by
    intro key
    constructor
    · intro map valid left right same
      change left = right at same
      subst right
      exact PartialObservedMapClosure.option_refl observation _
    · intro first second hf hs
      subst first
      subst second
      intro left right same
      change left = right at same
      subst right
      exact PartialObservedMapClosure.option_refl observation _
  captured := by
    intro code key call action before after inverse result called
    rw [actual_action action] at called
    by_cases inDomain : before ≤ 1
    · have same : flip before = after ∧ flip = inverse ∧ 0 = result := by
        simpa [callback, inDomain] using called
      obtain ⟨rfl, rfl, rfl⟩ := same
      have valid : before = 0 ∨ before = 1 := by omega
      rcases valid with rfl | rfl <;> exact ⟨rfl, rfl⟩
    · simp [callback, inDomain] at called
  forward := by
    intro code key call action
    rw [actual_action action]
    funext value
    by_cases inDomain : value ≤ 1 <;> simp [callback, inverseMap, inDomain, Except.toOption]

def component : Component Unit Bool := ⟨fun _ => false, fun _ => true, true⟩
def view : View Unit Unit := id
def inverse : I := .operate () () flip
def restriction : I := .restrict () ()
def empty : R := fun _ => none
def s1 := put empty () (fresh component none)
def s2 := mark s1 () (.reloading true [] view)
def supplied := write s2 () () (some 0)
def s3 := mark supplied () (.reloading false [restriction] view)
def operated := write s3 () () (some 1)
def s4 := mark operated () (.active [inverse, restriction] view)
def s5 := retire s4 ()
def s6 := mark s5 () (.unloading [inverse, restriction] view)
def s7 := mark (discharge Stages.undo [inverse, restriction] s6) () .inactive

def states : Nat → R
  | 0 => empty | 1 => s1 | 2 => s2 | 3 => s3
  | 4 => s4 | 5 => s5 | 6 => s6 | _ => s7

def events : Nat → Event Unit Unit Bool
  | 0 => .command (.insert () component)
  | 1 => .lifecycle .begin ()
  | 2 => .lifecycle .iter ()
  | 3 => .lifecycle .finish ()
  | 4 => .command (.retire ())
  | 5 => .lifecycle .leave ()
  | _ => .lifecycle .unload ()

private theorem no_requirements {state : R} {row : F} (found : state () = some row)
    (live : row.retired = false) (declares : row.component = component) : Target state () view := by
  rw [Target, found]
  exact ⟨live, fun key required => by rw [declares] at required; cases required⟩

def trace : Trace program 7 where
  state := states
  notes := cutNotes states (fun time => eventActor (events time))
  event := events
  start := rfl
  seed := rfl
  step time bounded := by
    have cuts : time = 0 ∨ time = 1 ∨ time = 2 ∨ time = 3 ∨ time = 4 ∨ time = 5 ∨ time = 6 := by omega
    apply And.intro ?_ rfl
    rcases cuts with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨rfl, by simp, fun _ _ => trivial⟩, rfl⟩
    · exact .begin s1 () (fresh component none) view rfl rfl (by change some _ ≠ none; simp)
        (no_requirements rfl rfl rfl)
    · exact .iter s2 supplied () { (fresh component none : F) with phase := .reloading true [] view }
        true [] view restriction false rfl rfl (no_requirements rfl rfl rfl)
        (.provide s2 () true _ () 0 rfl rfl rfl rfl)
    · exact .finish s3 operated () { (fresh component none : F) with
          phase := .reloading false [restriction] view, table := fun _ => some 0 }
        false [restriction] view inverse rfl rfl (no_requirements rfl rfl rfl)
        (.operate s3 () false () callback () 0 1 flip 0 rfl rfl rfl)
    · exact ⟨by change some _ ≠ none; simp, rfl⟩
    · exact .leave s5 () { (fresh component none : F) with
          phase := .active [inverse, restriction] view, retired := true, table := fun _ => some 1 }
        [inverse, restriction] view rfl rfl (fun invalid => Bool.noConfusion invalid.1)
    · refine ⟨{ (fresh component none : F) with
          phase := .unloading [inverse, restriction] view, retired := true, table := fun _ => some 1 },
        view, rfl, rfl, ?_, rfl⟩
      rintro ⟨name, different, _⟩
      cases name
      exact different rfl

/-- The source word contains an operation and then a restriction on the
same slot. Both take place on a bound slot and the last removes the binding. -/
theorem actual_unload_domains :
    InverseDefined meaning s6 inverse ∧
      InverseDefined meaning (replay (trace.notes 6).1 [⟨inverse, 4⟩] s6) restriction ∧
      tableAt (trace.state 7) () () = none := by
  have valid := saved_word_defined trace 6 (by decide) meaning ()
  refine ⟨valid [] ⟨inverse, 4⟩ [⟨restriction, 3⟩] rfl,
    valid [⟨inverse, 4⟩] ⟨restriction, 3⟩ [] rfl, rfl⟩

theorem partial_inverse_rejects_outside_input :
    ¬ InverseDefined meaning (write s6 () () (some 2)) inverse := by
  rintro ⟨input, output, atSlot, performed⟩
  have same : 2 = input := Option.some.inj atSlot
  subst input
  change (none : Option Nat) = some output at performed
  cases performed

theorem factored_unload : Factored meaning (trace.notes 6) (trace.event 6) (trace.state 6) (trace.state 7) :=
  trace_factorization trace meaning (by decide)

end Cordis.Repairs.ReplayBindingExample
