import Cordis.Renaming
import Cordis.Repairs.ScopedProgram

/-! The typed primitives transport the same data as the registry permutation.
For a fixed program the next code must agree on the two child outcomes;
non-child outcomes need no premise. -/
namespace Cordis.Repairs.FreshNameTransport
open TypedRegistry
open PaperEffectEquations (CoeffectOperations)
universe u
variable {Name Key Code : Type u} {V : Key → Type u} {ops : CoeffectOperations V}
local notation "P" => Renaming.Permutation Name
local notation "R" => Registry Name V Code
local notation "I" => Inverse Name V
local notation "Program" => Code → Instruction Name ops Code

def inverse (p : P) : I → I
  | .unit => .unit
  | .restrict owner key => .restrict (p.toFun owner) key
  | .operate owner key run => .operate (p.toFun owner) key run
  | .retire child => .retire (p.toFun child)

def phase (p : P) : Calculus.Phase Name Key Code I → Calculus.Phase Name Key Code I
  | .inactive => .inactive
  | .reloading code word view => .reloading code (word.map (inverse p)) (Renaming.view p view)
  | .active word view => .active (word.map (inverse p)) (Renaming.view p view)
  | .unloading word view => .unloading (word.map (inverse p)) (Renaming.view p view)

def fiber (p : P) (entry : Fiber Name V Code) : Fiber Name V Code :=
  { entry with parent := entry.parent.map p.toFun, phase := phase p entry.phase }

def registry (p : P) (state : R) : R :=
  fun name => (state (p.invFun name)).map (fiber p)

def outcome (p : P) : Outcome Name ops → Outcome Name ops
  | .child child => .child (p.toFun child)
  | other => other

@[simp] theorem outcome_symm (p : P) (reply : Outcome Name ops) :
    outcome p.symm (outcome p reply) = reply := by
  cases reply <;> simp [outcome, Renaming.Permutation.symm]

theorem outcome_injective (p : P) : Function.Injective (outcome (ops := ops) p) := by
  intro first second paired
  rw [← outcome_symm p first, ← outcome_symm p second, paired]

def program (p : P) (prog : Program) : Program := fun code =>
  { action := (prog code).action
    next := (prog code).next ∘ outcome p.symm }

theorem program_fixed_iff (p : P) (prog : Program) :
    program p prog = prog ↔
      ∀ code child, (prog code).next (.child (p.toFun child)) = (prog code).next (.child child) := by
  have selected (code : Code) (child : Name) :
      (program p prog code).next (.child (p.toFun child)) = (prog code).next (.child child) := by
    simp [program, outcome, Renaming.Permutation.symm]
  constructor
  · intro same code child
    exact (congrArg (fun prg : Program => (prg code).next (.child (p.toFun child))) same).symm.trans
      (selected code child)
  · intro same
    funext code
    have next_eq : (program p prog code).next = (prog code).next := by
      funext reply
      cases reply with
      | child name =>
        obtain ⟨original, rfl⟩ := p.surjective name
        exact (selected code original).trans (same code original).symm
      | unit | provision | operation => rfl
    change (Instruction.mk (prog code).action (program p prog code).next) = prog code
    rw [next_eq]

variable [DecidableEq Key]

theorem encode_inverse (p : P) (token : I) :
    encodeInverse ops (inverse p token) = Renaming.inverse p (encodeInverse ops token) := by
  cases token <;> rfl

theorem encode_phase (p : P) (current : Calculus.Phase Name Key Code I) :
    encodePhase ops (phase p current) = Renaming.phase p (encodePhase ops current) := by
  cases current <;> simp [phase, encodePhase, Renaming.phase, List.map_map, Function.comp_def, encode_inverse]

theorem encode_fiber (p : P) (entry : Fiber Name V Code) :
    encodeFiber ops (fiber p entry) = Renaming.fiber p (encodeFiber ops entry) := by
  simp [fiber, encodeFiber, Renaming.fiber, encode_phase]

theorem encode_registry (p : P) (state : R) :
    encodeRegistry ops (registry p state) = Renaming.registry p (encodeRegistry ops state) := by
  funext name
  simp [encodeRegistry, registry, Renaming.registry, Option.map_map, Function.comp_def, encode_fiber]

theorem encode_program (p : P) (prog : Program) :
    encodeProgram (program p prog) = Renaming.program p (encodeProgram prog) := by
  funext code
  have continuations : ∀ raw,
      (decodeOutcome ops raw).bind ((prog code).next ∘ outcome p.symm) =
        (decodeOutcome ops (Renaming.outcome p.symm raw)).bind (prog code).next := by
    intro raw
    cases raw with
    | unit => rfl
    | child => rfl
    | value value =>
      cases value with
      | inl v => cases v <;> rfl
      | inr v => cases v <;> rfl
  simp only [encodeProgram, Function.comp_apply, program, Renaming.program, encodeInstruction, continuations]

omit [DecidableEq Key] in
@[simp] theorem program_next (p : P) (prog : Program) (code : Code) (reply : Outcome Name ops) :
    (program p prog code).next (outcome p reply) = (prog code).next reply := by
  simp only [program, Function.comp_apply, outcome_symm]

omit [DecidableEq Key] in
theorem program_symm (p : P) (prog : Program) : program p.symm (program p prog) = prog := by
  funext code
  have same : (program p.symm (program p prog) code).next = (prog code).next := by
    funext reply
    simp only [program, Function.comp_apply, Renaming.Permutation.symm_symm, outcome_symm]
  cases current : prog code
  simp_all [program]

omit [DecidableEq Key] in
@[simp] theorem captured_child (p : P) (token : I) :
    capturedChild (inverse p token) = (capturedChild token).map p.toFun := by
  cases token <;> rfl

variable [DecidableEq Name]

omit [DecidableEq Name] in

theorem registry_symm (ops : CoeffectOperations V) (p : P) (state : R) :
    registry p.symm (registry p state) = state := by
  apply encodeRegistry_injective ops
  simp only [encode_registry, Renaming.registry_symm]

theorem undo_transport (ops : CoeffectOperations V) (p : P) (state : R) (token : I) :
    registry p (undo token state) = undo (inverse p token) (registry p state) := by
  apply encodeRegistry_injective ops
  simp only [encode_registry, encode_undo, encode_inverse, Renaming.undo_eq]

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem registry_at (p : P) (state : R) (name : Name) :
    registry p state (p.toFun name) = (state name).map (fiber p) := by simp [registry]

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem table_at (p : P) (state : R) (name : Name) (key : Key) :
    tableAt (registry p state) (p.toFun name) key = tableAt state name key := by
  unfold tableAt
  rw [registry_at]
  cases state name <;> rfl

omit [DecidableEq Name] [DecidableEq Key] in
theorem inverse_defined (p : P) (state : R) (token : I) :
    InverseDefined (registry p state) (inverse p token) ↔ InverseDefined state token := by
  cases token <;> simp [InverseDefined, inverse]

omit [DecidableEq Name] in
theorem location_at (ops : CoeffectOperations V) (p : P) (state : R) (actor : Name) (key : Key) :
    location (registry p state) (p.toFun actor) key =
      (location state actor key).map (fun pair => (p.toFun pair.1, pair.2)) := by
  have raw := Renaming.location_eq p (encodeRegistry ops state) actor key
  rw [← encode_registry, encode_location, encode_location, Option.map_map] at raw
  cases first : location (registry p state) (p.toFun actor) key <;>
    cases second : location state actor key <;>
    simp only [first, second, Option.map_some, Option.map_none, Function.comp_apply, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at raw ⊢
  rename_i left right
  exact Prod.ext raw.1 (TypedCoeffectReplay.pack_injective key raw.2)

omit [DecidableEq Name] in
theorem reply_at (p : P) (state : R) (prog : Program) (actor : Name) (draw : Option Name) (code : Code) :
    replyAt (program p prog) (p.toFun actor) (draw.map p.toFun) code (registry p state) =
      (replyAt prog actor draw code state).map (outcome p) := by
  cases action : (prog code).action with
  | unit | provide => simp [replyAt, program, action, outcome]
  | operate key name argument =>
    simp only [replyAt, program, action, location_at ops]
    cases located : location state actor key with
    | none => rfl
    | some pair =>
      obtain ⟨owner, value⟩ := pair
      cases called : (ops.operation key name argument).run value with
      | none => simp [called]
      | some result =>
        obtain ⟨changed, inverse, reply⟩ := result
        simp [called, outcome]
  | instantiate => cases draw <;> simp [replyAt, program, action, outcome]

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_related (p : P) (state : R) (observe : ∀ key, Setoid (V key)) (keys : Key → Prop) :
    TypedStateObservation.TablesRelatedAt observe keys state (registry p state) := by
  intro key _
  constructor
  · intro owner value found
    exact ⟨p.toFun owner, value, (table_at p state owner key).trans found, (observe key).refl value⟩
  · intro owner value found
    obtain ⟨original, rfl⟩ := p.surjective owner
    exact ⟨original, value, (table_at p state original key).symm.trans found, (observe key).refl value⟩

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_related_rename_right (p : P) (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (left right : R) :
    TypedStateObservation.TablesRelatedAt observe keys left (registry p right) ↔
      TypedStateObservation.TablesRelatedAt observe keys left right := by
  constructor
  · intro related key selected
    obtain ⟨forward, backward⟩ := related key selected
    constructor
    · intro owner value bound
      obtain ⟨other, found, there, compared⟩ := forward owner value bound
      obtain ⟨original, rfl⟩ := p.surjective other
      exact ⟨original, found, (table_at p right original key).symm.trans there, compared⟩
    · intro owner value bound
      exact backward (p.toFun owner) value ((table_at p right owner key).trans bound)
  · intro related key selected
    obtain ⟨forward, backward⟩ := related key selected
    constructor
    · intro owner value bound
      obtain ⟨other, found, there, compared⟩ := forward owner value bound
      exact ⟨p.toFun other, found, (table_at p right other key).trans there, compared⟩
    · intro owner value bound
      obtain ⟨original, rfl⟩ := p.surjective owner
      exact backward original value ((table_at p right original key).symm.trans bound)

omit [DecidableEq Name] [DecidableEq Key] in
theorem tables_related_rename (p : P) (observe : ∀ key, Setoid (V key)) (keys : Key → Prop)
    (left right : R) :
    TypedStateObservation.TablesRelatedAt observe keys (registry p left) (registry p right) ↔
      TypedStateObservation.TablesRelatedAt observe keys left right := by
  rw [tables_related_rename_right]
  have symm (a b : R) : TypedStateObservation.TablesRelatedAt observe keys a b ↔
      TypedStateObservation.TablesRelatedAt observe keys b a := by
    have reverse {a b : R} (same : TypedStateObservation.TablesRelatedAt observe keys a b) :
        TypedStateObservation.TablesRelatedAt observe keys b a := by
      intro key selected
      exact ⟨fun owner value found => by
        obtain ⟨other, paired, bound, compared⟩ := (same key selected).2 owner value found
        exact ⟨other, paired, bound, (observe key).symm compared⟩,
        fun owner value found => by
          obtain ⟨other, paired, bound, compared⟩ := (same key selected).1 owner value found
          exact ⟨other, paired, bound, (observe key).symm compared⟩⟩
    exact ⟨reverse, reverse⟩
  exact (symm _ _).trans ((tables_related_rename_right p observe keys right left).trans (symm _ _))

omit [DecidableEq Key] in
theorem birth_registry (p : P) (state : R) (actor child : Name)
    (component : Calculus.Component Key Code) :
    registry p (put state child (fresh component (some actor))) =
      put (registry p state) (p.toFun child) (fresh component (some (p.toFun actor))) := by
  funext name
  obtain ⟨original, rfl⟩ := p.surjective name
  rw [registry_at]
  by_cases same : original = child
  · subst original
    rw [put, put, if_pos rfl, if_pos rfl]
    rfl
  · simp [put, same]

omit [DecidableEq Name] [DecidableEq Key] in
theorem birth_insertable (p : P) {state : R} {actor child : Name}
    {component : Calculus.Component Key Code} (ready : Insertable state child component (some actor)) :
    Insertable (registry p state) (p.toFun child) component (some (p.toFun actor)) := by
  refine ⟨by simp [ready.1], ?_, ?_⟩
  · intro name same
    cases same
    simpa using ready.2.1 actor rfl
  · intro name key
    obtain ⟨original, rfl⟩ := p.surjective name
    rw [registry_at]
    have reserved := ready.2.2 original key
    cases found : state original with
    | none => trivial
    | some entry => simpa [found, fiber] using reserved

/-- Outcome translation keeps the original selected code and the actual
captured callback. The continuation itself belongs to the transported program. -/
theorem land_transport (p : P) {prog : Program} {actor : Name} {code : Code}
    {before after : R} {token : I} {next : Option Code}
    (landed : Land prog actor code before after token next) :
    Land (program p prog) (p.toFun actor) code (registry p before) (registry p after)
      (inverse p token) next := by
  have moved := Renaming.land_map p (encodeProgram prog) (land_encode ops landed)
  rw [← encode_program, ← encode_registry, ← encode_registry, ← encode_inverse] at moved
  obtain ⟨after', token', actual, endpoint, saved⟩ := land_decode ops moved
  cases encodeRegistry_injective ops endpoint
  cases encodeInverse_injective ops saved
  exact actual

/-- This test concerns the child outcome of the actual landing. A provision
or operation may use an arbitrary continuation on its dependent outcome. -/
theorem land_transport_same (p : P) {prog : Program} {actor : Name} {code : Code}
    {before after : R} {token : I} {next : Option Code}
    (landed : Land prog actor code before after token next)
    (compatible : ∀ child, token = .retire child →
      (prog code).next (.child (p.toFun child)) = next) :
    Land prog (p.toFun actor) code (registry p before) (registry p after) (inverse p token) next := by
  have moved := land_transport p landed
  have compatible' : ∀ child, inverse p token = .retire child → (prog code).next (.child child) = next := by
    intro child captured
    cases token with
    | retire original =>
      have same : p.toFun original = child := Inverse.retire.inj captured
      simpa only [same] using compatible original rfl
    | unit => cases captured
    | restrict => cases captured
    | operate => cases captured
  revert compatible'
  generalize inverse p token = movedToken at moved ⊢
  generalize registry p before = movedBefore at moved ⊢
  generalize registry p after = movedAfter at moved ⊢
  cases moved with
  | unit state name code action =>
    intro _
    exact .unit _ _ _ action
  | provide state name code entry key value action present declared absent =>
    intro _
    exact .provide _ _ _ _ _ _ action present declared absent
  | operate state name code key op argument owner before after inv result action located called =>
    intro _
    exact .operate _ _ _ _ _ _ _ _ _ _ _ action located called
  | instantiate state name code component child action ready =>
    intro agrees
    rw [← agrees child rfl]
    exact .instantiate _ _ _ _ _ action ready

theorem birth_selected {prog : Program} {before after : R} {actor child : Name} {code : Code}
    {next : Option Code} (landed : Land prog actor code before after (.retire child) next) :
    (prog code).next (.child child) = next := by
  cases landed
  rfl

/-- At a matched birth, continuation agreement is also necessary to land
with the same code. The saved name and component are those of the target
birth, with its actual insertability guard. -/
theorem birth_landing_iff {prog : Program} {state : R} {actor child : Name} {code : Code}
    {component : Calculus.Component Key Code} (action : (prog code).action = .instantiate component)
    (ready : Insertable state child component (some actor)) (next : Option Code) :
    Land prog actor code state (put state child (fresh component (some actor))) (.retire child) next ↔
      (prog code).next (.child child) = next := by
  constructor
  · exact birth_selected
  · rintro rfl
    exact .instantiate state actor code component child action ready

/-- A paired birth has the same payload and the renamed captured child.
The native landing has the original selected code exactly when the program's
two child outcomes select that same code. -/
theorem paired_birth_iff (p : P) {prog : Program} {state : R}
    {actor child : Name} {code : Code} {component : Calculus.Component Key Code}
    (action : (prog code).action = .instantiate component)
    (ready : Insertable state child component (some actor)) :
    Land prog (p.toFun actor) code (registry p state)
      (registry p (put state child (fresh component (some actor)))) (inverse p (.retire child))
      ((prog code).next (.child child)) ↔
      (prog code).next (.child (p.toFun child)) = (prog code).next (.child child) := by
  rw [birth_registry]
  exact birth_landing_iff action (birth_insertable p ready) _

/-- All native stages of the mixed iterator carry their chosen codes and
saved tokens to the renamed program. Different draws occur in the same
sequence of component declarations. -/
theorem landings_transport (p : P) {prog : Program} {actor : Name} {code : Code}
    {before after : R} {tokens : List I}
    (landed : ScopedProgram.Landings prog actor code before after tokens) :
    ScopedProgram.Landings (program p prog) (p.toFun actor) code
      (registry p before) (registry p after) (tokens.map (inverse p)) := by
  induction landed with
  | last head => exact .last (land_transport p head)
  | next head _ tail => exact .next (land_transport p head) tail

/-- A fixed program can keep its selected codes whenever the two outcomes of
each successful birth agree. There is no restriction on provisions or calls
to key-dependent operations. -/
theorem landings_transport_same (p : P) {prog : Program} {actor : Name} {code : Code}
    {before after : R} {tokens : List I}
    (landed : ScopedProgram.Landings prog actor code before after tokens)
    (agrees : ∀ (current : Code) (source target : R) (child : Name) (next : Option Code),
      Land prog actor current source target (.retire child) next →
      (prog current).next (.child (p.toFun child)) = next) :
    ScopedProgram.Landings prog (p.toFun actor) code
      (registry p before) (registry p after) (tokens.map (inverse p)) := by
  have head {current : Code} {source target : R} {token : I} {next : Option Code}
      (step : Land prog actor current source target token next) :
      Land prog (p.toFun actor) current (registry p source) (registry p target) (inverse p token) next := by
    apply land_transport_same p step
    intro child captured
    subst token
    exact agrees current source target child next step
  induction landed with
  | last step => exact .last (head step)
  | next step _ tail => exact .next (head step) tail

/-- Fix all names except the two alternative draws. Any old occurrences in
parents, views, or captured tokens still have to be transported. -/
def swap (first second : Name) : P := by
  let exchange := fun name => if name = first then second else if name = second then first else name
  have involutive : ∀ n, exchange (exchange n) = n := by
    intro name
    by_cases left : name = first
    · subst name
      by_cases same : first = second
      · subst second
        simp [exchange]
      · simp [exchange, Ne.symm same]
    · by_cases right : name = second
      · simp [exchange, right]
      · simp [exchange, left, right]
  exact ⟨exchange, exchange, involutive, involutive⟩

@[simp] theorem swap_first (first second : Name) : (swap first second).toFun first = second := by
  simp [swap]

@[simp] theorem swap_other {first second name : Name} (left : name ≠ first) (right : name ≠ second) :
    (swap first second).toFun name = name := by simp [swap, left, right]

end Cordis.Repairs.FreshNameTransport
