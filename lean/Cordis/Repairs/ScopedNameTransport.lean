import Cordis.Repairs.FreshNameTransport

/-! Transport the complete scoped iterator across a name bijection, including
its partial inverse probes and every outcome-selected domain link. -/
namespace Cordis.Repairs.ScopedNameTransport
open TypedRegistry ScopedEffects FreshNameTransport
open PaperEffectEquations (CoeffectOperations)
open Iterators (OptionRel)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
variable [DecidableEq Name] [DecidableEq Key]
local notation "P" => Renaming.Permutation Name
local notation "R" => Registry Name V Code
local notation "Dom" => R → Prop
variable {source target : Registry Name V Code → Prop} {O : Type u}

def domain (p : P) (admitted : Dom) : Dom := fun state => admitted (registry p.symm state)

def moveState (ops : CoeffectOperations V) (p : P) (input : State source) : State (domain p source) :=
  ⟨registry p input.val, by simpa only [domain, registry_symm ops] using input.property⟩

def originalState (p : P) (input : State (domain p source)) : State source :=
  ⟨registry p.symm input.val, input.property⟩

omit [DecidableEq Name] in
@[simp] theorem original_move (p : P) (input : State source) :
    originalState p (moveState ops p input) = input :=
  Subtype.ext (registry_symm ops p input.val)

omit [DecidableEq Name] in
@[simp] theorem move_original (p : P) (input : State (domain p source)) :
    moveState ops p (originalState p input) = input :=
  Subtype.ext (registry_symm ops p.symm input.val)

def moveSaved (ops : CoeffectOperations V) (p : P) (saved : Saved target) : Saved (domain p target) :=
  fun input => (saved (originalState p input)).map (moveState ops p)

private def moveResult (ops : CoeffectOperations V) (p : P)
    (result : State target × Saved target × O) : State (domain p target) × Saved (domain p target) × O :=
  (moveState ops p result.1, moveSaved ops p result.2.1, result.2.2)

def effect (ops : CoeffectOperations V) (p : P) (head : Effect source target O) :
    Effect (domain p source) (domain p target) O :=
  ⟨fun input => (head.run (originalState p input)).map (moveResult ops p)⟩

omit [DecidableEq Name] in

@[simp] theorem effect_run (p : P) (head : Effect source target O) (input : State source) :
    (effect ops p head).run (moveState ops p input) = (head.run input).map (moveResult ops p) := by
  simp [effect]

omit [DecidableEq Name] in
private theorem observed_move (p : P) (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (left : State source) (right : State target) :
    Observed observe keys (moveState ops p left) (moveState ops p right) ↔ Observed observe keys left right :=
  tables_related_rename p observe keys left.val right.val

private theorem option_map {X Y X' Y' : Type u} {related : X → Y → Prop} {moved : X' → Y' → Prop}
    {f : X → X'} {g : Y → Y'} {a : Option X} {b : Option Y} (same : OptionRel related a b)
    (law : ∀ x y, related x y → moved (f x) (g y)) :
    OptionRel moved (a.map f) (b.map g) := by
  cases a <;> cases b <;> simp_all [OptionRel]

omit [DecidableEq Name] in

theorem lawful (p : P) {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
    {head : Effect source target O} (law : Lawful observe keys head) :
    Lawful observe keys (effect ops p head) := by
  constructor
  · intro input output saved reply called
    change (head.run (originalState p input)).map (moveResult ops p) = _ at called
    obtain ⟨⟨result, inverse, originalReply⟩, found, same⟩ := Option.map_eq_some_iff.mp called
    cases same
    obtain ⟨restored, undone, compared⟩ := law.recover _ _ _ _ found
    refine ⟨moveState ops p restored, ?_, ?_⟩
    · simp [moveSaved, undone]
    · change Observed observe keys (moveState ops p restored) input
      rw [← move_original (ops := ops) p input]
      exact (observed_move p observe keys _ _).mpr compared
  · intro left right related
    obtain ⟨a, rfl⟩ : ∃ a, moveState ops p a = left := ⟨originalState p left, move_original p left⟩
    obtain ⟨b, rfl⟩ : ∃ b, moveState ops p b = right := ⟨originalState p right, move_original p right⟩
    rw [effect_run, effect_run]
    refine option_map (f := moveResult ops p) (g := moveResult ops p)
      (law.respect a b ((observed_move p observe keys a b).mp related)) ?_
    rintro ⟨outA, saveA, replyA⟩ ⟨outB, saveB, replyB⟩ ⟨outputs, saved, replies⟩
    refine ⟨(observed_move (ops := ops) p observe keys _ _).mpr outputs, ?_, replies⟩
    intro probeA probeB related
    obtain ⟨a, rfl⟩ : ∃ a, moveState ops p a = probeA := ⟨originalState p probeA, move_original p probeA⟩
    obtain ⟨b, rfl⟩ : ∃ b, moveState ops p b = probeB := ⟨originalState p probeB, move_original p probeB⟩
    simp only [moveResult, moveSaved, original_move]
    exact option_map (saved a b ((observed_move p observe keys a b).mp related))
      (fun a b => (observed_move p observe keys a b).mpr)

omit [DecidableEq Name] in
/-- Compare both the forward result and the partial inverse against a
renamed head. Each inverse is tested in its own output domain, while the
comparison observes only the tables. -/
theorem effect_respects_renamed (p : P) {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}
    {head : Effect source target O} (law : Lawful observe keys head)
    (left : State source) (right : State (domain p source)) (related : Observed observe keys left right) :
    OptionRel (fun a b => Observed observe keys a.1 b.1 ∧
      (∀ x y, Observed observe keys x y →
        OptionRel (Observed observe keys) (a.2.1 x) (b.2.1 y)) ∧ a.2.2 = b.2.2)
      (head.run left) ((effect ops p head).run right) := by
  obtain ⟨original, rfl⟩ : ∃ input, moveState ops p input = right :=
    ⟨originalState p right, move_original p right⟩
  have initial : Observed observe keys left original :=
    (tables_related_rename_right p observe keys left.val original.val).mp related
  have unchanged : (head.run left).map id = head.run left := congrFun Option.map_id _
  rw [effect_run, ← unchanged]
  refine option_map (law.respect left original initial) ?_
  rintro ⟨outA, savedA, replyA⟩ ⟨outB, savedB, replyB⟩ ⟨outputs, saves, replies⟩
  refine ⟨(tables_related_rename_right p observe keys outA.val outB.val).mpr outputs, ?_, replies⟩
  intro probe renamed same
  obtain ⟨originalProbe, rfl⟩ : ∃ input, moveState ops p input = renamed :=
    ⟨originalState p renamed, move_original p renamed⟩
  have relatedProbe : Observed observe keys probe originalProbe :=
    (tables_related_rename_right p observe keys probe.val originalProbe.val).mp same
  simp only [moveResult, moveSaved, original_move]
  change OptionRel (Observed observe keys) (savedA probe) ((savedB originalProbe).map (moveState ops p))

  have unchanged : (savedA probe).map id = savedA probe := congrFun Option.map_id _
  rw [← unchanged]
  exact option_map (saves probe originalProbe relatedProbe)
    (fun a b compared => (tables_related_rename_right p observe keys a.val b.val).mpr compared)

variable {program : Code → Instruction Name ops Code} {actor : Name} {code : Code}
variable {observe : ∀ key, Setoid (V key)} {keys : Key → Prop}

theorem realizes (p : P) {head : Effect source target O} {reply : O → Outcome Name ops}
    {draw : Option Name} (original : Realizes program actor code reply head draw) :
    Realizes (FreshNameTransport.program p program) (p.toFun actor) code
      (outcome p ∘ reply) (effect ops p head) (draw.map p.toFun) := by
  constructor
  · intro input output saved result called
    change (head.run (originalState p input)).map (moveResult ops p) = _ at called
    obtain ⟨⟨landed, inverseMap, originalReply⟩, found, same⟩ := Option.map_eq_some_iff.mp called
    cases same
    obtain ⟨token, executed, inverseSound, drawn, exactReply⟩ := original.sound _ _ _ _ found
    have roundTrip (state : R) : registry p (registry p.symm state) = state := registry_symm ops p.symm state
    refine ⟨FreshNameTransport.inverse p token, ?_, ⟨?_, ?_⟩, by rw [captured_child, drawn], ?_⟩
    · simpa only [moveResult, moveState, originalState, roundTrip, Function.comp_apply, program_next] using
        land_transport p executed
    · intro probe restored applied
      change (inverseMap (originalState p probe)).map (moveState ops p) = some restored at applied
      obtain ⟨before, inverseApplied, rfl⟩ := Option.map_eq_some_iff.mp applied
      change registry p before.val = undo (FreshNameTransport.inverse p token) probe.val
      rw [inverseSound.value _ _ inverseApplied, undo_transport ops p]
      simp only [originalState, roundTrip]
    · intro probe
      have scope := inverse_defined p (originalState p probe).val token
      change InverseDefined (registry p (registry p.symm probe.val)) _ ↔
        InverseDefined (originalState p probe).val token at scope
      rw [roundTrip] at scope
      rw [scope, ← inverseSound.defined (originalState p probe)]
      change (∃ restored, (inverseMap (originalState p probe)).map (moveState ops p) = some restored) ↔ _
      constructor
      · rintro ⟨restored, applied⟩
        obtain ⟨before, found, _⟩ := Option.map_eq_some_iff.mp applied
        exact ⟨before, found⟩
      · rintro ⟨before, found⟩
        exact ⟨moveState ops p before, by rw [found]; rfl⟩
    · have actual := reply_at p (originalState p input).val program actor draw code
      rw [exactReply] at actual
      simpa only [originalState, roundTrip, Option.map_some, Function.comp_apply] using actual
  · intro input after token next landed drawn
    have moved := land_transport p.symm landed
    rw [program_symm, show p.symm.toFun (p.toFun actor) = actor from p.left_inv actor] at moved
    have selected : capturedChild (inverse p.symm token) = draw := by
      rw [captured_child, drawn]
      cases draw <;> simp [Renaming.Permutation.symm]
    obtain ⟨result, called⟩ := original.complete (originalState p input) moved selected
    exact ⟨moveResult ops p result, by change (head.run (originalState p input)).map _ = _; rw [called]; rfl⟩

theorem stable_domain (p : P) (stable : ScopedRollback.Stable ops source) :
    ScopedRollback.Stable ops (domain p source) := by
  constructor
  · intro prg actor code before after token next landed admissible
    exact stable.land (land_transport p.symm landed) admissible
  · intro token state admissible
    unfold domain at *
    rw [undo_transport ops p.symm]
    exact stable.undo _ _ admissible

def head (p : P) (original : ScopedProgram.Head program actor observe keys code source target O) :
    ScopedProgram.Head (FreshNameTransport.program p program) (p.toFun actor) observe keys code
      (domain p source) (domain p target) O where
  effect := effect ops p original.effect
  reply := outcome p ∘ original.reply
  reply_injective := fun _ _ same => original.reply_injective (outcome_injective p same)
  draw := original.draw.map p.toFun
  lawful := lawful p original.lawful
  realizes := realizes p original.realizes
  outputStable reply next selected := stable_domain p
    (original.outputStable reply next (by simpa only [Function.comp_apply, program_next] using selected))

/-- Pull each continuation domain back along the inverse name map. The link
for a moved head is the original link applied to the inverse-renamed call. -/
def iterator (p : P) {code : Code} {source : R → Prop}
    (it : ScopedProgram.Iterator program actor observe keys code source) :
    ScopedProgram.Iterator (FreshNameTransport.program p program) (p.toFun actor)
      observe keys code (domain p source) :=
  match it with
  | .stage original entry tail link =>
    .stage (head p original) (fun reply => domain p (entry reply))
      (fun reply next selected => iterator p (tail reply next (by
        simpa only [head, Function.comp_apply, program_next] using selected)))
      (by
        intro input output inverse reply next called selected
        change (original.effect.run (originalState p input)).map (moveResult ops p) = _ at called
        obtain ⟨⟨result, saved, nativeReply⟩, found, same⟩ := Option.map_eq_some_iff.mp called
        cases same
        change entry nativeReply (registry p.symm (registry p result.val))
        rw [registry_symm ops p]
        exact link _ _ _ _ _ found (by
          simpa only [head, Function.comp_apply, program_next] using selected))

/-- The whole evaluation, including a failure or a successfully chosen tail,
is the original evaluation transported to the renamed input. -/
theorem execute_transport (p : P)
    (it : ScopedProgram.Iterator program actor observe keys code source)
    (input : State source) :
    (iterator p it).execute (moveState ops p input) = (it.execute input).map (registry p) := by
  induction it with
  | stage original entry tail link ih =>
    simp only [iterator, ScopedProgram.Iterator.execute, head]
    split
    · rename_i missed
      rw [effect_run, Option.map_eq_none_iff] at missed
      split
      · rfl
      · rename_i _ _ _ appeared
        rw [missed] at appeared
        cases appeared
    · rename_i movedOutput movedSaved movedReply movedCalled
      rw [effect_run] at movedCalled
      obtain ⟨⟨output, saved, reply⟩, found, same⟩ := Option.map_eq_some_iff.mp movedCalled
      cases same
      simp only [Function.comp_apply]
      split
      · rename_i terminal
        rw [program_next] at terminal
        split
        · rename_i absent
          rw [absent] at found
          cases found
        · rename_i other otherSaved otherReply otherCalled
          obtain ⟨rfl, rfl, rfl⟩ := (by simpa only [Prod.mk.injEq] using Option.some.inj (found.symm.trans otherCalled) :
            output = other ∧ saved = otherSaved ∧ reply = otherReply)
          split
          · rfl
          · rename_i continuation continuing
            rw [terminal] at continuing
            cases continuing
      · rename_i next selected
        rw [program_next] at selected
        split
        · rename_i absent
          rw [absent] at found
          cases found
        · rename_i other otherSaved otherReply otherCalled
          obtain ⟨rfl, rfl, rfl⟩ := (by simpa only [Prod.mk.injEq] using Option.some.inj (found.symm.trans otherCalled) :
            output = other ∧ saved = otherSaved ∧ reply = otherReply)
          split
          · rename_i stopped
            rw [stopped] at selected
            cases selected
          · rename_i following continues
            have sameCode := Option.some.inj (selected.symm.trans continues)
            subst following
            exact ih reply next selected ⟨output.val, link _ _ _ _ _ found selected⟩

/-- Distinct underlying registries may be compared with different fixed name
draws. The right iterator and its input domain are the transported ones.
Only union-table observation is used to compare the initial probes. -/
theorem execute_respects_renamed (p : P)
    (it : ScopedProgram.Iterator program actor observe keys code source)
    (left : State source) (right : State (domain p source)) (related : Observed observe keys left right) :
    OptionRel (TypedStateObservation.TablesRelatedAt observe keys)
      (it.execute left) ((iterator p it).execute right) := by
  obtain ⟨original, rfl⟩ : ∃ original, moveState ops p original = right :=
    ⟨originalState p right, move_original p right⟩
  have initial : Observed observe keys left original :=
    (tables_related_rename_right p observe keys left.val original.val).mp related
  rw [execute_transport]
  simpa only [Option.map_id] using
    option_map (f := id) (g := registry p) (it.execute_respects left original initial)
      (fun first second compared => (tables_related_rename_right p observe keys first second).mpr compared)

/-- An unchanged program admits the transported scoped plan whenever the
name change preserves its continuation on child outcomes. -/
def iterator_same_program (p : P)
    (agrees : ∀ current child, (program current).next (.child (p.toFun child)) =
      (program current).next (.child child))
    (it : ScopedProgram.Iterator program actor observe keys code source) :
    ScopedProgram.Iterator program (p.toFun actor) observe keys code (domain p source) :=
  (program_fixed_iff p program).mpr agrees ▸ iterator p it

private theorem execute_cast_program {first second : Code → Instruction Name ops Code}
    (same : first = second) (it : ScopedProgram.Iterator first actor observe keys code source)
    (input : State source) :
    (show ScopedProgram.Iterator second actor observe keys code source from same ▸ it).execute input =
      it.execute input := by
  cases same
  rfl

theorem execute_respects_same_program (p : P)
    (agrees : ∀ current child, (program current).next (.child (p.toFun child)) =
      (program current).next (.child child))
    (it : ScopedProgram.Iterator program actor observe keys code source)
    (left : State source) (right : State (domain p source)) (related : Observed observe keys left right) :
    OptionRel (TypedStateObservation.TablesRelatedAt observe keys)
      (it.execute left) ((iterator_same_program p agrees it).execute right) := by
  unfold iterator_same_program
  rw [execute_cast_program]
  exact execute_respects_renamed p it left right related

end Cordis.Repairs.ScopedNameTransport
