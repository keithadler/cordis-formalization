import Cordis.Renaming
import Cordis.StageRecovery
import Cordis.Labeled

/-! The literal registry-index/parent/committed-view action displayed in
Lemma61, distinguished from the full nominal action already proved in Renaming.
No accumulator or iterator capture is transported by this displayed action.

The witness below uses actual full registries, not a frozen table store. Names
are unbounded atoms, keys are empty, and Gamma consists of all finite rooted
registry trees. Definition51's projection is therefore the unique empty table.
Every state/function observation is proved from that exact projection. Actual
instantiation and retirement still change nonempty registry/control data. -/
namespace Cordis.RenamingLiteral
noncomputable section
open Calculus Stages Effects Iterators Renaming StageRecovery

abbrev Name := Nat
abbrev Code := Bool
abbrev R := Registry Name Empty Unit Code (Inverse Name Empty Unit) Empty
abbrev F := Fiber Name Empty Unit Code (Inverse Name Empty Unit) Empty

/-- Precisely the fields named in the displayed definition of chi·gamma.
Accumulator words retain their exact functions, including captured atoms. -/
def phase (p : Permutation Name) : Phase Name Empty Code (Inverse Name Empty Unit) →
    Phase Name Empty Code (Inverse Name Empty Unit)
  | .inactive => .inactive
  | .reloading code accumulator view => .reloading code accumulator (Renaming.view p view)
  | .active accumulator view => .active accumulator (Renaming.view p view)
  | .unloading accumulator view => .unloading accumulator (Renaming.view p view)

def fiber (p : Permutation Name) (entry : F) : F :=
  { entry with parent := entry.parent.map p.toFun, phase := phase p entry.phase }

def registry (p : Permutation Name) (state : R) : R :=
  fun name => (state (p.invFun name)).map (fiber p)

def FiniteDomain (state : R) : Prop :=
  ∃ names : List Name, ∀ name, state name ≠ none → name ∈ names

theorem put_finite (state : R) (name : Name) (entry : F) (finite : FiniteDomain state) :
    FiniteDomain (put state name entry) := by
  obtain ⟨names, covers⟩ := finite
  refine ⟨name :: names, ?_⟩
  intro other present
  by_cases same : other = name
  · simp [same]
  · exact List.mem_cons_of_mem _ (covers other (by simpa [put, same] using present))

theorem modify_finite (state : R) (name : Name) (change : F → F) (finite : FiniteDomain state) :
    FiniteDomain (Calculus.modify state name change) := by
  obtain ⟨names, covers⟩ := finite
  refine ⟨names, ?_⟩
  intro other present
  apply covers other
  intro absent
  apply present
  by_cases same : other = name
  · subst other; simp [Calculus.modify, absent]
  · simp [Calculus.modify, same, absent]

abbrev Gamma := {state : R // Safety.Tree state ∧ FiniteDomain state}

/-- Freshness is available at every admissible registry, not just at the
particular test history. The numeric construction only proves this existential;
no language primitive computes or inspects an atom. -/
theorem fresh_exists (state : Gamma) : ∃ name, state.val name = none := by
  obtain ⟨names, covers⟩ := state.property.2
  refine ⟨names.max?.getD 0 + 1, ?_⟩
  classical
  by_cases absent : state.val (names.max?.getD 0 + 1) = none
  · exact absent
  · have bound := List.le_max?_getD_of_mem (k := 0) (covers _ absent)
    omega

def freshAtom (state : Gamma) : Name := Classical.choose (fresh_exists state)
theorem freshAtom_absent (state : Gamma) : state.val (freshAtom state) = none :=
  Classical.choose_spec (fresh_exists state)

def preferFresh (preferred : Name) (state : Gamma) : Name := by
  classical
  exact if state.val preferred = none then preferred else freshAtom state

theorem preferFresh_absent (preferred : Name) (state : Gamma) : state.val (preferFresh preferred state) = none := by
  simp only [preferFresh]
  split
  · assumption
  · exact freshAtom_absent state

instance valueSetoid : Setoid Unit := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem projected_all (left right : R) : ProjectedRelated (fun _ => True) left right := by
  intro key
  exact nomatch key

/-- Definition33 read at precisely Definition51, with no owner/declaration
frame or restriction of input registries. -/
instance gammaSetoid : Setoid Gamma where
  r left right := ProjectedRelated (fun _ => True) left.val right.val
  iseqv := ⟨fun _ => projected_all _ _, fun _ => projected_all _ _, fun _ _ => projected_all _ _⟩

def retireGamma (child : Name) (state : Gamma) : Gamma :=
  ⟨Calculus.retire state.val child, ⟨Safety.modify_tree state.val child _ (fun _ => rfl) state.property.1,
    modify_finite state.val child _ state.property.2⟩⟩

/-- The primitive's actual legal action, with identity extension when its
insertion guard fails. No name is inspected or computed by the iterator. -/
def birthEffect (actor child : Name) (component : Component Empty Code) : Effect Gamma := by
  classical
  exact ⟨fun state => if ready : Insertable state.val child component (some actor) then
    (⟨put state.val child (fresh component (some actor)), ⟨Safety.insert_tree _ _ _ _ state.property.1 ready, put_finite _ _ _ state.property.2⟩⟩,
      retireGamma child)
    else (state, id)⟩

def birthIterator (actor child : Name) (component : Component Empty Code) : Iterator Gamma :=
  embed (birthEffect actor child component)

theorem birth_actual (actor child : Name) (component : Component Empty Code) (state : Gamma)
    (ready : Insertable state.val child component (some actor)) :
    ((birthIterator actor child component).effect.run state).1.val =
        put state.val child (fresh component (some actor)) ∧
    (∀ input : Gamma, (((birthIterator actor child component).effect.run state).2 input).val =
      Calculus.retire input.val child) ∧
    (birthIterator actor child component).next state = none := by
  simp [birthIterator, embed, birthEffect, ready, retireGamma, Iterator.effect, Iterator.next]

/-- A rule may draw a different fresh atom at every registry. This family covers
all such choices and carries the actual chosen atom into the returned inverse. -/
def drawnBirthEffect (actor : Name) (draw : Gamma → Name) (component : Component Empty Code) : Effect Gamma :=
  ⟨fun state => (birthEffect actor (draw state) component).run state⟩

def drawnBirthIterator (actor : Name) (draw : Gamma → Name) (component : Component Empty Code) : Iterator Gamma :=
  embed (drawnBirthEffect actor draw component)

theorem drawn_birth_witnessed (actor : Name) (draw : Gamma → Name) (component : Component Empty Code) :
    WitnessedIterator (drawnBirthIterator actor draw component) := by
  apply witnessed_embed
  constructor
  · intro state; exact projected_all _ _
  · intro left right _
    exact ⟨projected_all _ _, fun {_ _} _ => projected_all _ _⟩

theorem fresh_draw_ready (actor : Name) (draw : Gamma → Name) (component : Component Empty Code)
    (freshAtEveryState : ∀ state : Gamma, state.val (draw state) = none)
    (state : Gamma) (actorPresent : state.val actor ≠ none) :
    Insertable state.val (draw state) component (some actor) := by
  refine ⟨freshAtEveryState state, ?_, ?_⟩
  · intro parent same; cases same; exact actorPresent
  · intro _ key; exact nomatch key

theorem drawn_birth_actual (actor : Name) (draw : Gamma → Name) (component : Component Empty Code)
    (freshAtEveryState : ∀ state : Gamma, state.val (draw state) = none)
    (state : Gamma) (actorPresent : state.val actor ≠ none) :
    ((drawnBirthIterator actor draw component).effect.run state).1.val =
      put state.val (draw state) (fresh component (some actor)) ∧
    (∀ input : Gamma, (((drawnBirthIterator actor draw component).effect.run state).2 input).val =
      Calculus.retire input.val (draw state)) ∧
    (drawnBirthIterator actor draw component).next state = none :=
  birth_actual actor (draw state) component state (fresh_draw_ready actor draw component freshAtEveryState state actorPresent)

end
end Cordis.RenamingLiteral
