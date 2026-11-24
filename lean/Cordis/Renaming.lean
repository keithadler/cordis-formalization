import Cordis.WellFormed

/-!
Lemma61: transport along an arbitrary bijection of fiber names. Renaming reaches
captured inverse owners/children as well as parents and committed views. Program
continuations are transported by precomposing child outcomes with the inverse
bijection; no equivariance hypothesis is imposed on arbitrary callback functions.
-/
namespace Cordis.Renaming
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}

structure Permutation (Name : Type u) where
  toFun : Name → Name
  invFun : Name → Name
  left_inv : ∀ n, invFun (toFun n) = n
  right_inv : ∀ n, toFun (invFun n) = n

namespace Permutation
@[simp] theorem inv_to (p : Permutation Name) (n : Name) : p.invFun (p.toFun n) = n := p.left_inv n
@[simp] theorem to_inv (p : Permutation Name) (n : Name) : p.toFun (p.invFun n) = n := p.right_inv n

def symm (p : Permutation Name) : Permutation Name :=
  ⟨p.invFun, p.toFun, p.right_inv, p.left_inv⟩

@[simp] theorem symm_symm (p : Permutation Name) : p.symm.symm = p := rfl

def identity : Permutation Name := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def trans (first second : Permutation Name) : Permutation Name :=
  ⟨second.toFun ∘ first.toFun, first.invFun ∘ second.invFun, fun _ => by simp, fun _ => by simp⟩

theorem injective (p : Permutation Name) {a b : Name} (h : p.toFun a = p.toFun b) : a = b := by
  have eq := congrArg p.invFun h
  simpa using eq

@[simp] theorem eq_iff (p : Permutation Name) (a b : Name) : p.toFun a = p.toFun b ↔ a = b :=
  ⟨p.injective, congrArg p.toFun⟩

theorem surjective (p : Permutation Name) (n : Name) : ∃ m, p.toFun m = n :=
  ⟨p.invFun n, p.right_inv n⟩
end Permutation

def inverse (p : Permutation Name) : Inverse Name Key Value → Inverse Name Key Value
  | .unit => .unit
  | .restrict n k => .restrict (p.toFun n) k
  | .operate n k f => .operate (p.toFun n) k f
  | .retire n => .retire (p.toFun n)

def outcome (p : Permutation Name) : Outcome Name Value → Outcome Name Value
  | .unit => .unit
  | .value v => .value v
  | .child n => .child (p.toFun n)

def view (p : Permutation Name) (v : View Name Key) : View Name Key := p.toFun ∘ v

def phase (p : Permutation Name) : Phase Name Key Code (Inverse Name Key Value) →
    Phase Name Key Code (Inverse Name Key Value)
  | .inactive => .inactive
  | .reloading c a v => .reloading c (a.map (inverse p)) (view p v)
  | .active a v => .active (a.map (inverse p)) (view p v)
  | .unloading a v => .unloading (a.map (inverse p)) (view p v)

local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error

def fiber (p : Permutation Name) (f : F) : F :=
  { f with parent := f.parent.map p.toFun, phase := phase p f.phase }

def registry (p : Permutation Name) (r : R) : R :=
  fun n => (r (p.invFun n)).map (fiber p)

/-- Renaming laws, oriented from nested transports to a single transport. -/
@[simp] theorem inverse_identity (token : Inverse Name Key Value) :
    inverse Permutation.identity token = token := by cases token <;> rfl

theorem inverse_trans (first second : Permutation Name) (token : Inverse Name Key Value) :
    inverse second (inverse first token) = inverse (first.trans second) token := by
  cases token <;> rfl

@[simp] theorem phase_identity (status : Phase Name Key Code (Inverse Name Key Value)) :
    phase Permutation.identity status = status := by
  have tokens : inverse (Permutation.identity : Permutation Name) =
      (id : Inverse Name Key Value → _) := funext inverse_identity
  cases status <;> simp only [phase, tokens, List.map_id] <;> rfl

theorem phase_trans (first second : Permutation Name)
    (status : Phase Name Key Code (Inverse Name Key Value)) :
    phase second (phase first status) = phase (first.trans second) status := by
  have tokens : inverse second ∘ inverse first =
      (inverse (first.trans second) : Inverse Name Key Value → _) := funext (inverse_trans first second)
  cases status <;> simp [phase, view, Permutation.trans, List.map_map, tokens] <;> rfl

@[simp] theorem fiber_identity (row : F) : fiber Permutation.identity row = row := by
  simp only [fiber, phase_identity]
  simp only [Permutation.identity, Option.map_id, id_eq]

theorem fiber_trans (first second : Permutation Name) (row : F) :
    fiber second (fiber first row) = fiber (first.trans second) row := by
  cases row
  simp only [fiber, Option.map_map, phase_trans]
  rfl

@[simp] theorem registry_identity (r : R) : registry Permutation.identity r = r := by
  funext name
  change (r name).map (fiber Permutation.identity) = r name
  cases r name <;> simp only [Option.map_none, Option.map_some, fiber_identity]

theorem registry_trans (first second : Permutation Name) (r : R) :
    registry second (registry first r) = registry (first.trans second) r := by
  have fibers : fiber second ∘ fiber first = (fiber (first.trans second) : F → _) :=
    funext (fiber_trans first second)
  funext name
  simp only [registry, Option.map_map, fibers, Permutation.trans, Function.comp_apply]

/-- Code identities are unchanged; an observed child name is translated back
before calling the original continuation. -/
def program (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error) :
    Code → Instruction Name Key Value Code Error := fun c =>
  { action := (prg c).action
    next := fun o => (prg c).next (outcome p.symm o)
 }

@[simp] theorem inverse_symm (p : Permutation Name) (i : Inverse Name Key Value) :
    inverse p.symm (inverse p i) = i := by
  cases i <;> simp [inverse, Permutation.symm]

@[simp] theorem outcome_symm (p : Permutation Name) (o : Outcome Name Value) :
    outcome p.symm (outcome p o) = o := by
  cases o <;> simp [outcome, Permutation.symm]

@[simp] theorem view_symm (p : Permutation Name) (v : View Name Key) :
    view p.symm (view p v) = v := by
  funext k
  simp [view, Permutation.symm]

@[simp] theorem phase_symm (p : Permutation Name)
    (s : Phase Name Key Code (Inverse Name Key Value)) : phase p.symm (phase p s) = s := by
  cases s <;> simp [phase, List.map_map, Function.comp_def]

@[simp] theorem fiber_symm (p : Permutation Name) (f : F) : fiber p.symm (fiber p f) = f := by
  cases f with
  | mk c pa t rt ph =>
    simp only [fiber, phase_symm]
    cases pa <;> simp [Permutation.symm]

@[simp] theorem registry_at (p : Permutation Name) (r : R) (n : Name) :
    registry p r (p.toFun n) = (r n).map (fiber p) := by simp [registry]

@[simp] theorem registry_symm (p : Permutation Name) (r : R) : registry p.symm (registry p r) = r := by
  funext n
  change Option.map (fiber p.symm) ((r (p.invFun (p.toFun n))).map (fiber p)) = r n
  simp [Option.map_map, Function.comp_def]

@[simp] theorem program_next (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error)
    (c : Code) (o : Outcome Name Value) : (program p prg c).next (outcome p o) = (prg c).next o := by
  simp [program]

@[simp] theorem program_symm (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error) :
    program p.symm (program p prg) = prg := by
  funext c
  simp only [program]
  congr 1 <;> funext o <;> cases o <;> simp [outcome, Permutation.symm]

@[simp] theorem phase_committed (p : Permutation Name)
    (s : Phase Name Key Code (Inverse Name Key Value)) :
    (phase p s).committed = s.committed.map (view p) := by cases s <;> rfl

@[simp] theorem phase_available (p : Permutation Name)
    (s : Phase Name Key Code (Inverse Name Key Value)) : (phase p s).available ↔ s.available := by
  cases s <;> rfl

@[simp] theorem phase_inactive (p : Permutation Name)
    (s : Phase Name Key Code (Inverse Name Key Value)) : phase p s = .inactive ↔ s = .inactive := by
  cases s <;> simp [phase]

@[simp] theorem fresh_fiber (p : Permutation Name) (c : Component Key Code) (parent : Option Name) :
    fiber p (fresh c parent : F) = fresh c (parent.map p.toFun) := rfl

variable [DecidableEq Name] [DecidableEq Key]

omit [DecidableEq Key] in
theorem put_eq (p : Permutation Name) (r : R) (n : Name) (f : F) :
    registry p (put r n f) = put (registry p r) (p.toFun n) (fiber p f) := by
  funext m
  obtain ⟨m, rfl⟩ := p.surjective m
  by_cases h : m = n <;> simp [put, h]

omit [DecidableEq Key] in
theorem erase_eq (p : Permutation Name) (r : R) (n : Name) :
    registry p (erase r n) = erase (registry p r) (p.toFun n) := by
  funext m
  obtain ⟨m, rfl⟩ := p.surjective m
  by_cases h : m = n <;> simp [erase, h]

omit [DecidableEq Key] in
theorem modify_eq (p : Permutation Name) (r : R) (n : Name) (change renamed : F → F)
    (commutes : ∀ f, fiber p (change f) = renamed (fiber p f)) :
    registry p (Calculus.modify r n change) = Calculus.modify (registry p r) (p.toFun n) renamed := by
  funext m
  obtain ⟨m, rfl⟩ := p.surjective m
  by_cases same : m = n
  · subst m
    simp [Calculus.modify, Option.map_map, Function.comp_def, commutes]
  · simp [Calculus.modify, same]

omit [DecidableEq Key] in
theorem mark_eq (p : Permutation Name) (r : R) (n : Name) (s) :
    registry p (mark r n s) = mark (registry p r) (p.toFun n) (phase p s) :=
  modify_eq p r n _ _ (fun _ => rfl)

omit [DecidableEq Key] in
theorem retire_eq (p : Permutation Name) (r : R) (n : Name) :
    registry p (Calculus.retire r n) = Calculus.retire (registry p r) (p.toFun n) :=
  modify_eq p r n _ _ (fun _ => rfl)

theorem write_eq (p : Permutation Name) (r : R) (n : Name) (k : Key) (v : Option Value) :
    registry p (write r n k v) = write (registry p r) (p.toFun n) k v :=
  modify_eq p r n _ _ (fun _ => rfl)

theorem undo_eq (p : Permutation Name) (r : R) (i : Inverse Name Key Value) :
    registry p (Stages.undo i r) = Stages.undo (inverse p i) (registry p r) := by
  cases i with
  | unit => rfl
  | restrict n k => exact write_eq p r n k none
  | operate n k f => exact modify_eq p r n _ _ (fun _ => rfl)
  | retire n => exact retire_eq p r n

theorem discharge_eq (p : Permutation Name) (r : R) (a : List (Inverse Name Key Value)) :
    registry p (discharge Stages.undo a r) = discharge Stages.undo (a.map (inverse p)) (registry p r) := by
  induction a generalizing r with
  | nil => rfl
  | cons i a ih => simp only [discharge, List.map_cons, ih, undo_eq]

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem target_iff (p : Permutation Name) (r : R) (n : Name) (v : View Name Key) :
    Target (registry p r) (p.toFun n) (view p v) ↔ Target r n v := by
  cases hn : r n with
  | none => simp [Target, hn]
  | some f =>
    simp only [Target, registry_at, hn, Option.map_some, fiber]
    constructor
    · rintro ⟨hr, ht⟩
      refine ⟨hr, ?_⟩
      intro k hk
      have h := ht k hk
      dsimp only [view, Function.comp_apply] at h
      cases hp : r (v k) with
      | none => simp [hp] at h
      | some provider => simpa [registry_at, hp, fiber] using h
    · rintro ⟨hr, ht⟩
      refine ⟨hr, ?_⟩
      intro k hk
      have h := ht k hk
      dsimp only [view, Function.comp_apply]
      cases hp : r (v k) with
      | none => simp [hp] at h
      | some provider => simpa [registry_at, hp, fiber] using h

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem errorFree_iff (p : Permutation Name) (r : R) (n : Name) :
    ErrorFree (registry p r) (p.toFun n) ↔ ErrorFree r n := by
  cases hn : r n <;> simp [ErrorFree, hn]

omit [DecidableEq Name] [DecidableEq Key] in
theorem insertable_map (p : Permutation Name) (r : R) (n : Name) (c : Component Key Code)
    (parent : Option Name) (h : Insertable r n c parent) :
    Insertable (registry p r) (p.toFun n) c (parent.map p.toFun) := by
  refine ⟨by simp [h.1], ?_, ?_⟩
  · intro renamed hp
    cases old : parent with
    | none => simp [old] at hp
    | some original =>
      have eq : p.toFun original = renamed := Option.some.inj (by simpa [old] using hp)
      subst renamed
      simpa using h.2.1 original old
  · intro other k
    obtain ⟨other, rfl⟩ := p.surjective other
    have separated := h.2.2 other k
    cases ho : r other with
    | none => simp [ho]
    | some entry => simpa [registry_at, ho, fiber] using separated

omit [DecidableEq Name] [DecidableEq Key] in
theorem removable_map (p : Permutation Name) (r : R) (n : Name) (h : Removable r n) :
    Removable (registry p r) (p.toFun n) := by
  cases hn : r n with
  | none => simp [Removable, hn] at h
  | some f =>
    simp only [Removable, hn] at h
    simp only [Removable, registry_at, hn, Option.map_some, fiber]
    refine ⟨h.1, (phase_inactive p f.phase).mpr h.2.1, h.2.2.1, ?_⟩
    intro child
    obtain ⟨child, rfl⟩ := p.surjective child
    have hc := h.2.2.2 child
    cases ch : r child with
    | none => simp [ch]
    | some cf =>
      simp only [ch] at hc
      simp only [registry_at, ch, Option.map_some, fiber]
      cases pa : cf.parent <;> simp_all

omit [DecidableEq Name] [DecidableEq Key] in
theorem relied_map (p : Permutation Name) (r : R) (n : Name) (h : Relied r n) :
    Relied (registry p r) (p.toFun n) := by
  obtain ⟨consumer, ne, h⟩ := h
  refine ⟨p.toFun consumer, fun eq => ne (p.injective eq), ?_⟩
  cases hc : r consumer with
  | none => simp [hc] at h
  | some cf =>
    simp only [hc] at h
    cases cv : cf.phase.committed with
    | none => simp [cv] at h
    | some v =>
      simp only [cv] at h
      obtain ⟨k, required, provider⟩ := h
      refine ?_
      simp only [registry_at, hc, Option.map_some, fiber, phase_committed, cv, Option.map_some]
      exact ⟨k, required, congrArg p.toFun provider⟩

omit [DecidableEq Name] [DecidableEq Key] in
@[simp] theorem relied_iff (p : Permutation Name) (r : R) (n : Name) :
    Relied (registry p r) (p.toFun n) ↔ Relied r n := by
  constructor
  · intro h
    have hr := relied_map p.symm (registry p r) (p.toFun n) h
    rw [registry_symm] at hr
    change Relied r (p.invFun (p.toFun n)) at hr
    simpa using hr
  · exact relied_map p r n

omit [DecidableEq Name] [DecidableEq Key] in
theorem location_eq (p : Permutation Name) (r : R) (n : Name) (k : Key) :
    location (registry p r) (p.toFun n) k =
      (location r n k).map (fun pair => (p.toFun pair.1, pair.2)) := by
  cases hn : r n with
  | none => simp [location, Stages.bindingOwner, hn]
  | some f =>
    by_cases provides : f.component.provides k = true
    · cases hv : f.table k <;> simp [location, Stages.bindingOwner, hn, fiber, provides, hv]
    · by_cases requires : f.component.requires k = true
      · cases hc : f.phase.committed with
        | none => simp [location, Stages.bindingOwner, hn, fiber, provides, requires, hc]
        | some v =>
          cases hp : r (v k) with
          | none => simp [location, Stages.bindingOwner, hn, fiber, provides, requires, hc, view, registry, hp]
          | some provider =>
            cases hv : provider.table k <;>
              simp [location, Stages.bindingOwner, hn, fiber, provides, requires, hc, view, registry, hp, hv]
      · simp [location, Stages.bindingOwner, hn, fiber, provides, requires]

theorem performed_map (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error)
    {n : Name} {c : Code} {r s : R} {i : Inverse Name Key Value} {o : Outcome Name Value}
    (h : Performed prg n c r s i o) :
    Performed (program p prg) (p.toFun n) c (registry p r) (registry p s) (inverse p i) (outcome p o) := by
  cases h with
  | unit r n c action => exact .unit _ _ _ action
  | provide r n c f k v action present allowed absent =>
    simpa only [write_eq, inverse, outcome] using
      (Execution.provide (program := program p prg) (registry p r) (p.toFun n) c (fiber p f) k v action
        (by simp [present]) allowed absent)
  | operate r n c k run owner before after inv result action located returned =>
    simpa only [write_eq, inverse, outcome] using
      (Execution.operate (program := program p prg) (registry p r) (p.toFun n) c k run (p.toFun owner) before after inv result action
        (by simp [location_eq, located]) returned)
  | instantiate r n c component child action allowed =>
    simpa only [put_eq, fresh_fiber, Option.map_some, inverse, outcome] using
      (Execution.instantiate (program := program p prg) (registry p r) (p.toFun n) c component (p.toFun child) action
        (insertable_map p r child component (some n) allowed))

theorem land_has_outcome (prg : Code → Instruction Name Key Value Code Error)
    {n : Name} {c : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (h : Land prg n c r s i next) :
    ∃ o, Performed prg n c r s i o ∧ (prg c).next o = next := by
  cases h with
  | unit r n c action => exact ⟨.unit, .unit r n c action, rfl⟩
  | provide r n c f k v action present allowed absent =>
    exact ⟨.value v, .provide r n c f k v action present allowed absent, rfl⟩
  | operate r n c k run owner before after inv result action located returned =>
    exact ⟨.value result, .operate r n c k run owner before after inv result action located returned, rfl⟩
  | instantiate r n c component child action allowed =>
    exact ⟨.child child, .instantiate r n c component child action allowed, rfl⟩

theorem land_map (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error)
    {n : Name} {c : Code} {r s : R} {i : Inverse Name Key Value} {next : Option Code}
    (h : Land prg n c r s i next) :
    Land (program p prg) (p.toFun n) c (registry p r) (registry p s) (inverse p i) next := by
  obtain ⟨o, performed, hn⟩ := land_has_outcome prg h
  have mapped := (performed_map p prg performed).toLand (program p prg)
  simpa only [program_next, hn] using mapped

/-- Structural transport for the nine rules; the primitive landing-map obligation
is discharged below for both actual stage semantics, not supplied by clients. -/
theorem step_transport (p : Permutation Name)
    {land land' : Landing (Name := Name) (Key := Key) (Value := Value)
      (Code := Code) (Undo := Inverse Name Key Value) (Error := Error)}
    (lands : ∀ n c r s i next, land n c r s i next →
      land' (p.toFun n) c (registry p r) (registry p s) (inverse p i) next)
    {r s : R} (h : Calculus.Step land Stages.undo r s) :
    Calculus.Step land' Stages.undo (registry p r) (registry p s) := by
  cases h with
  | insert n component parent allowed =>
    simpa only [put_eq, fresh_fiber] using
      (Calculus.Step.insert (land := land') (undo := Stages.undo) (registry p r)
        (p.toFun n) component (parent.map p.toFun) (insertable_map p r n component parent allowed))
  | retire n present =>
    simpa only [retire_eq] using
      (Calculus.Step.retire (land := land') (undo := Stages.undo) (registry p r) (p.toFun n)
        (by simpa using present))
  | remove n ready =>
    simpa only [erase_eq] using
      (Calculus.Step.remove (land := land') (undo := Stages.undo) (registry p r) (p.toFun n)
        (removable_map p r n ready))
  | begin n f v present inactive errorFree target =>
    simpa only [mark_eq, phase, List.map_nil] using
      (Calculus.Step.begin (land := land') (undo := Stages.undo) (registry p r)
        (p.toFun n) (fiber p f) (view p v) (by simp [present])
        (by simp [fiber, inactive, phase]) ((errorFree_iff p r n).mpr errorFree)
        ((target_iff p r n v).mpr target))
  | iter s n f c a v i next present reloading target landing =>
    simpa only [mark_eq, phase, List.map_cons] using
      (Calculus.Step.iter (land := land') (undo := Stages.undo) (registry p r) (registry p s)
        (p.toFun n) (fiber p f) c (a.map (inverse p)) (view p v) (inverse p i) next
        (by simp [present]) (by simp [fiber, reloading, phase])
        ((target_iff p r n v).mpr target) (lands _ _ _ _ _ _ landing))
  | finish s n f c a v i present reloading target landing =>
    simpa only [mark_eq, phase, List.map_cons] using
      (Calculus.Step.finish (land := land') (undo := Stages.undo) (registry p r) (registry p s)
        (p.toFun n) (fiber p f) c (a.map (inverse p)) (view p v) (inverse p i)
        (by simp [present]) (by simp [fiber, reloading, phase])
        ((target_iff p r n v).mpr target) (lands _ _ _ _ _ _ landing))
  | divert s n f c a v tail present reloading target alternative =>
    have mapped : (registry p s = registry p r ∧ tail.map (inverse p) = []) ∨
        ∃ i next, land' (p.toFun n) c (registry p r) (registry p s) i next ∧
          tail.map (inverse p) = [i] := by
      rcases alternative with ⟨same, nil⟩ | ⟨i, next, landing, single⟩
      · exact .inl ⟨congrArg (registry p) same, by simp [nil]⟩
      · exact .inr ⟨inverse p i, next, lands _ _ _ _ _ _ landing, by simp [single]⟩
    simpa only [mark_eq, phase, List.map_append] using
      (Calculus.Step.divert (land := land') (undo := Stages.undo) (registry p r) (registry p s)
        (p.toFun n) (fiber p f) c (a.map (inverse p)) (view p v) (tail.map (inverse p))
        (by simp [present]) (by simp [fiber, reloading, phase])
        (fun ht => target ((target_iff p r n v).mp ht)) mapped)
  | leave n f a v present active target =>
    simpa only [mark_eq, phase] using
      (Calculus.Step.leave (land := land') (undo := Stages.undo) (registry p r)
        (p.toFun n) (fiber p f) (a.map (inverse p)) (view p v)
        (by simp [present]) (by simp [fiber, active, phase])
        (fun ht => target ((target_iff p r n v).mp ht)))
  | unload n f a v present unloading free =>
    simpa only [mark_eq, discharge_eq, phase] using
      (Calculus.Step.unload (land := land') (undo := Stages.undo) (registry p r)
        (p.toFun n) (fiber p f) (a.map (inverse p)) (view p v)
        (by simp [present]) (by simp [fiber, unloading, phase])
        (fun hr => free ((relied_iff p r n).mp hr)))

theorem step_map (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error)
    {r s : R} (h : Calculus.Step (Land prg) Stages.undo r s) :
    Calculus.Step (Land (program p prg)) Stages.undo (registry p r) (registry p s) :=
  step_transport p (fun _ _ _ _ _ _ h => land_map p prg h) h

/-- Both directions for the actual nine-rule paper semantics. -/
theorem step_equivariant (p : Permutation Name) (prg : Code → Instruction Name Key Value Code Error)
    (r s : R) : Calculus.Step (Land prg) Stages.undo r s ↔
      Calculus.Step (Land (program p prg)) Stages.undo (registry p r) (registry p s) := by
  constructor
  · exact step_map p prg
  · intro h
    have back := step_map p.symm (program p prg) h
    simpa only [program_symm, registry_symm] using back

omit [DecidableEq Name] [DecidableEq Key] in
theorem present_original (p : Permutation Name) (r : R) (n : Name) (f : F)
    (h : registry p r n = some f) : ∃ original, r (p.invFun n) = some original ∧ fiber p original = f := by
  cases ho : r (p.invFun n) with
  | none => simp [registry, ho] at h
  | some original =>
    exact ⟨original, rfl, Option.some.inj (by simpa [registry, ho] using h)⟩

omit [DecidableEq Name] [DecidableEq Key] in
/-- All four Definition63 clauses transport; no inference from a finite oracle. -/
theorem wellFormed_map (p : Permutation Name) (r : R) (h : WellFormed.WellFormed r) :
    WellFormed.WellFormed (registry p r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro child entry parent present parentOf
    obtain ⟨original, old, eq⟩ := present_original p r child entry present
    subst entry
    change original.parent.map p.toFun = some parent at parentOf
    cases pa : original.parent with
    | none => simp [pa] at parentOf
    | some op =>
      have eq : p.toFun op = parent := Option.some.inj (by simpa [pa] using parentOf)
      subst parent
      simpa using h.1 (p.invFun child) original op old pa
  · intro a b fa fb ha hb ne k provided
    obtain ⟨oa, hoa, ca⟩ := present_original p r a fa ha
    obtain ⟨ob, hob, cb⟩ := present_original p r b fb hb
    subst fa fb
    apply h.2.1 (p.invFun a) (p.invFun b) oa ob hoa hob ?_ k provided
    intro eq
    exact ne (by simpa using congrArg p.toFun eq)
  · intro n f v k present committed required
    obtain ⟨original, old, eq⟩ := present_original p r n f present
    subst f
    change (phase p original.phase).committed = some v at committed
    rw [phase_committed] at committed
    cases cv : original.phase.committed with
    | none => simp [cv] at committed
    | some ov =>
      have eq : view p ov = v := Option.some.inj (by simpa [cv] using committed)
      subst v
      obtain ⟨provider, hp, installed⟩ := h.2.2 (p.invFun n) original ov k old cv required
      refine ⟨fiber p provider, ?_, ?_⟩
      · simp [view, hp]
      · cases hi : provider.phase.committed with
        | none => exact False.elim (installed hi)
        | some ov => simp [fiber, hi]

omit [DecidableEq Name] [DecidableEq Key] in
theorem wellFormed_equivariant (p : Permutation Name) (r : R) :
    WellFormed.WellFormed r ↔ WellFormed.WellFormed (registry p r) := by
  constructor
  · exact wellFormed_map p r
  · intro h
    simpa only [registry_symm] using wellFormed_map p.symm (registry p r) h

end Cordis.Renaming
