import Cordis.RenamingLiteral
import Cordis.Results.GlobalSupport

/-!
Theorem 80(1), PDF p. 54: an obstruction to its simultaneous requirements
that ALL orchestration steps keep their original order and that orchestration
at externally inserted fibers precede EVERY lifecycle step.

There are no coeffect keys. P's only stage instantiates a terminal unit child C;
Q is another terminal unit root. The legal history is

  Insert P; Begin P; Finish P (birth C); Retire C; Insert Q; Begin Q; Finish Q.

The endpoint is quiet. Both root episodes remain open; C never starts an
episode. All components are total on their empty provisions. External inserts
are roots, no name is reused, and no program branches on the allocated name.

Any alleged canonical history must retire C before inserting Q, because it
preserves the external command order. But inserting Q must precede every
lifecycle step, including whichever step first creates C. Retirement requires
C already to exist. The contradiction below is proved from the nine transition
rules, not assumed as an ordering axiom.

This refutes the stated canonical ordering, not confluence under a repaired
ordering statement. The global iterator witnesses below use precisely the
empty Definition 51 projection on all finite rooted registries.
-/
namespace Cordis.CanonicalOrderCounterexample
noncomputable section
open Calculus Stages Effects Iterators RenamingLiteral

def P : Name := 0
def C : Name := 1
def Q : Name := 2
def view : View Name Empty := fun key => nomatch key
def unitComponent : Component Empty Code := ⟨fun _ => false, fun _ => false, false⟩
def parentComponent : Component Empty Code := ⟨fun _ => false, fun _ => false, true⟩
def program (code : Code) : Instruction Name Empty Unit Code Empty :=
  ⟨if code then .instantiate unitComponent else .unit, fun _ => none⟩

def s0 : R := fun _ => none
def s1 : R := put s0 P (fresh parentComponent none)
def s2 : R := mark s1 P (.reloading true [] view)
def birth : R := put s2 C (fresh unitComponent (some P))
def s3 : R := mark birth P (.active [.retire C] view)
def s4 : R := Calculus.retire s3 C
def s5 : R := put s4 Q (fresh unitComponent none)
def s6 : R := mark s5 Q (.reloading false [] view)
def s7 : R := mark s6 Q (.active [.unit] view)

theorem birth_ready : Insertable s2 C unitComponent (some P) :=
  ⟨rfl, by intro parent same; cases same; exact Option.noConfusion, fun _ key => nomatch key⟩

def trace : Indexed.Trace program s0 7 where
  state
    | 0 => s0 | 1 => s1 | 2 => s2 | 3 => s3
    | 4 => s4 | 5 => s5 | 6 => s6 | _ => s7
  rule
    | 0 | 4 => .insert | 1 | 5 => .begin | 3 => .retire | _ => .finish
  actor
    | 0 | 1 | 2 => P | 3 => C | _ => Q
  start := rfl
  step := by
    intro t bounded
    have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .insert s0 P parentComponent none ⟨rfl, by simp, fun _ key => nomatch key⟩
    · exact .begin s1 P (fresh parentComponent none) view rfl rfl
        (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
    · exact .finish s2 birth P
        { (fresh parentComponent none : F) with phase := .reloading true [] view }
        true [] view (.retire C) rfl rfl ⟨rfl, fun key => nomatch key⟩
        (.instantiate s2 P true unitComponent C rfl birth_ready)
    · exact .retire s3 C (by change some _ ≠ none; simp)
    · exact .insert s4 Q unitComponent none ⟨rfl, by simp, fun _ key => nomatch key⟩
    · exact .begin s5 Q (fresh unitComponent none) view rfl rfl
        (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
    · exact .finish s6 s6 Q
        { (fresh unitComponent none : F) with phase := .reloading false [] view }
        false [] view .unit rfl rfl ⟨rfl, fun key => nomatch key⟩ (.unit s6 Q false rfl)

theorem root_insertions : PaperLifecycleClaims.RootInsertions trace := by
  intro t bounded label
  have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨_, rfl, rfl⟩ | cases label

theorem states_rooted : ∀ t, t ≤ 7 → Safety.Tree (trace.state t) := by
  intro t bounded
  induction t with
  | zero => exact Safety.empty_tree
  | succ t ih =>
    exact Safety.step_tree program (trace.step t bounded).toCalculus (ih (by omega))

theorem states_wellFormed (t : Nat) (bounded : t ≤ 7) :
    WellFormed.WellFormed (trace.state t) :=
  ⟨(states_rooted t bounded).1,
    (fun _ _ _ _ _ _ _ key => nomatch key), (fun _ _ _ key => nomatch key)⟩

theorem states_finite : ∀ t, t ≤ 7 → FiniteDomain (trace.state t) := by
  intro t bounded
  refine ⟨[P, C, Q], ?_⟩
  intro name present
  by_cases hp : name = P
  · simp [hp]
  by_cases hc : name = C
  · simp [hc]
  by_cases hq : name = Q
  · simp [hq]
  have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact False.elim (present (by
    simp [trace, s0, s1, s2, birth, s3, s4, s5, s6, s7,
      put, mark, Calculus.modify, Calculus.retire, hp, hc, hq]))

/-- Totality is universal, not only checked at the exhibited endpoint:
there is no key that any finishing activation could fail to install. -/
theorem total_everywhere (state : R) : SupportAtQuiescence.TotalProvision state :=
  fun _ _ _ _ key => nomatch key

theorem quiet : Progress.Quiet s7 := by
  intro name fiber found
  by_cases hp : name = P
  · subst name
    have same : { (fresh parentComponent none : F) with phase := .active [.retire C] view } = fiber :=
      Option.some.inj found
    subst fiber
    exact ⟨rfl, fun key => nomatch key⟩
  by_cases hc : name = C
  · subst name
    have same : { (fresh unitComponent (some P) : F) with retired := true } = fiber :=
      Option.some.inj found
    subst fiber
    intro _ target
    cases target.1
  by_cases hq : name = Q
  · subst name
    have same : { (fresh unitComponent none : F) with phase := .active [.unit] view } = fiber :=
      Option.some.inj found
    subst fiber
    exact ⟨rfl, fun key => nomatch key⟩
  simp [s7, s6, s5, s4, s3, birth, s2, s1, s0, mark, put,
    Calculus.modify, Calculus.retire, hp, hc, hq] at found

theorem support_wellFounded : WellFounded (PaperLifecycleClaims.supportEdge s7) := by
  apply Subrelation.wf (r := fun a b : Name => a < b) _ Nat.lt_wfRel.wf
  rintro parent child ⟨_, _, dependency | ancestry⟩
  · obtain ⟨key, _⟩ := dependency
    exact nomatch key
  · by_cases hp : child = P
    · subst child; cases ancestry
    by_cases hc : child = C
    · subst child
      have eq : P = parent := Option.some.inj ancestry
      subst parent
      decide
    by_cases hq : child = Q
    · subst child; cases ancestry
    simp [s7, s6, s5, s4, s3, birth, s2, s1, s0, mark, put,
      Calculus.modify, Calculus.retire, hp, hc, hq] at ancestry

theorem support_exact : SupportAtQuiescence.Solution s7 (fun name => name = P ∨ name = Q) := by
  intro name
  constructor
  · rintro (rfl | rfl)
    · exact ⟨_, rfl, rfl, .inl rfl, fun key => nomatch key⟩
    · exact ⟨_, rfl, rfl, .inl rfl, fun key => nomatch key⟩
  · rintro ⟨fiber, found, live, _, _⟩
    by_cases hp : name = P
    · exact .inl hp
    by_cases hq : name = Q
    · exact .inr hq
    by_cases hc : name = C
    · subst name
      have same : { (fresh unitComponent (some P) : F) with retired := true } = fiber :=
        Option.some.inj found
      subst fiber
      cases live
    simp [s7, s6, s5, s4, s3, birth, s2, s1, s0, mark, put,
      Calculus.modify, Calculus.retire, hp, hc, hq] at found

theorem no_closed_episodes (name : Name) (b u : Nat) : ¬ Indexed.EpisodeAt trace name b u := by
  intro episode
  have installed := episode.installed u episode.ordered (Nat.le_refl _)
  have vanished := episode.after
  have indices : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 := by
    have := episode.bounded; omega
  by_cases hp : name = P <;> by_cases hc : name = C <;> by_cases hq : name = Q <;>
    rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [trace, ControlFrame.viewAt, s0, s1, s2, birth, s3, s4, s5, s6, s7,
      put, mark, Calculus.modify, Calculus.retire, fresh, Phase.committed, P, C, Q]

/-- The actual terminal unit/birth iterators are globally witnessed.
No nominal or declaration-sensitive observation is added. -/
def meaning (actor : Name) (draw : Gamma → Name) (code : Code) : Iterator Gamma :=
  if code then drawnBirthIterator actor draw unitComponent else embed Effects.identity

theorem meaning_witnessed (actor : Name) (draw : Gamma → Name) (code : Code) :
    WitnessedIterator (meaning actor draw code) := by
  cases code
  · exact witnessed_embed witnessed_identity
  · exact drawn_birth_witnessed actor draw unitComponent

def beforeBirth : Gamma := ⟨s2, states_rooted 2 (by decide), states_finite 2 (by decide)⟩

/-- The witness implements the concrete child creation and the captured
retirement inverse, and returns no continuation. Freshness is global. -/
theorem birth_meaning_matches :
    ((meaning P (preferFresh C) true).effect.run beforeBirth).1.val = birth ∧
    (∀ input : Gamma, (((meaning P (preferFresh C) true).effect.run beforeBirth).2 input).val =
      Calculus.retire input.val C) ∧
    (meaning P (preferFresh C) true).next beforeBirth = none := by
  have actual := drawn_birth_actual P (preferFresh C) unitComponent (preferFresh_absent C)
    beforeBirth (by change some _ ≠ none; simp)
  have selected : preferFresh C beforeBirth = C := by simp [preferFresh, beforeBirth, s2, s1, s0, mark, Calculus.modify, put, C, P]
  simpa only [meaning, Bool.true_eq, if_true, selected] using actual

def External (rule : Labeled.Rule) : Prop :=
  rule = .insert ∨ rule = .retire ∨ rule = .remove

/-- A deliberately weaker necessary condition than retaining the same
commands: their labels/actors and total original order must be preserved.
Not constraining component payloads or the endpoint strengthens the refutation. -/
structure SameExternalOrder {last : Nat} (replay : Indexed.Trace program s0 last) where
  insertP : Nat
  retireC : Nat
  insertQ : Nat
  orderP : insertP < retireC
  orderC : retireC < insertQ
  bounded : insertQ < last
  first : replay.rule insertP = .insert ∧ replay.actor insertP = P
  second : replay.rule retireC = .retire ∧ replay.actor retireC = C
  third : replay.rule insertQ = .insert ∧ replay.actor insertQ = Q
  exhaustive : ∀ t, t < last → External (replay.rule t) →
    t = insertP ∨ t = retireC ∨ t = insertQ

def original_commands : SameExternalOrder trace where
  insertP := 0
  retireC := 3
  insertQ := 4
  orderP := by decide
  orderC := by decide
  bounded := by decide
  first := ⟨rfl, rfl⟩
  second := ⟨rfl, rfl⟩
  third := ⟨rfl, rfl⟩
  exhaustive := by
    intro t bounded external
    have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [External, trace]

private theorem insertP_preserves_absence {before after : R}
    (step : Labeled.Step program .insert P before after) (absent : before C = none) :
    after C = none := by
  cases step with
  | insert _ _ _ _ _ => simpa [put, C, P] using absent

private theorem retireC_requires_presence {before after : R}
    (step : Labeled.Step program .retire C before after) : before C ≠ none := by
  cases step with
  | retire _ _ present => exact present

/-- Even just Q's insertion cannot precede all lifecycle steps in any legal
replay that preserves all three external commands in their original order. -/
theorem no_canonical_replay {last : Nat} (replay : Indexed.Trace program s0 last)
    (commands : SameExternalOrder replay)
    (rootFirst : ∀ t, t < last → ¬ External (replay.rule t) → commands.insertQ < t) : False := by
  have absent : ∀ t, t ≤ commands.retireC → replay.state t C = none := by
    intro t bound
    induction t with
    | zero => rw [replay.start]; rfl
    | succ t ih =>
      have bounded : t < last := by have := commands.bounded; have := commands.orderC; omega
      have external : External (replay.rule t) := by
        by_cases lifecycle : External (replay.rule t)
        · exact lifecycle
        · have := rootFirst t bounded lifecycle
          have := commands.orderC
          omega
      have atP : t = commands.insertP := by
        have := commands.exhaustive t bounded external
        have := commands.orderC
        omega
      have step := replay.step t bounded
      have label : replay.rule t = .insert := atP.symm ▸ commands.first.1
      have actor : replay.actor t = P := atP.symm ▸ commands.first.2
      rw [label, actor] at step
      have missing := ih (by omega)
      exact insertP_preserves_absence step missing
  have step := replay.step commands.retireC (by have := commands.bounded; have := commands.orderC; omega)
  rw [commands.second.1, commands.second.2] at step
  exact retireC_requires_presence step (absent _ (Nat.le_refl _))

/-! A concrete repair of THIS history. Moving Insert Q across Retire C gives
Insert P; Insert Q; Begin P; Finish P/birth C; Retire C; Begin Q; Finish Q.
This preserves the relative order of the two root commands and reaches the
identical endpoint. It necessarily changes the total external command order.
It is not a proof of Theorem 80 for arbitrary histories under that amendment. -/

def rootsInserted : R := put s1 Q (fresh unitComponent none)
def earlyBegin : R := mark rootsInserted P (.reloading true [] view)
def earlyBirth : R := put earlyBegin C (fresh unitComponent (some P))
def earlyFinish : R := mark earlyBirth P (.active [.retire C] view)

theorem early_retire_same : Calculus.retire earlyFinish C = s5 := by
  funext name
  by_cases hp : name = P <;> by_cases hc : name = C <;> by_cases hq : name = Q <;>
    simp_all [earlyFinish, earlyBirth, earlyBegin, rootsInserted,
      s0, s1, s2, birth, s3, s4, s5, put, mark, Calculus.modify, Calculus.retire, P, C, Q]

def reorderedTrace : Indexed.Trace program s0 7 where
  state
    | 0 => s0 | 1 => s1 | 2 => rootsInserted | 3 => earlyBegin
    | 4 => earlyFinish | 5 => s5 | 6 => s6 | _ => s7
  rule
    | 0 | 1 => .insert | 2 | 5 => .begin | 4 => .retire | _ => .finish
  actor
    | 0 | 2 | 3 => P | 4 => C | _ => Q
  start := rfl
  step := by
    intro t bounded
    have indices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
    rcases indices with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact trace.step 0 (by decide)
    · exact .insert s1 Q unitComponent none ⟨rfl, by simp, fun _ key => nomatch key⟩
    · exact .begin rootsInserted P (fresh parentComponent none) view rfl rfl
        (by change some _ ≠ none; simp) ⟨rfl, fun key => nomatch key⟩
    · exact .finish earlyBegin earlyBirth P
        { (fresh parentComponent none : F) with phase := .reloading true [] view }
        true [] view (.retire C) rfl rfl ⟨rfl, fun key => nomatch key⟩
        (.instantiate earlyBegin P true unitComponent C rfl
          ⟨rfl, by intro parent same; cases same; exact Option.noConfusion,
            fun _ key => nomatch key⟩)
    · rw [← early_retire_same]
      exact .retire earlyFinish C (by change some _ ≠ none; simp)
    · exact trace.step 5 (by decide)
    · exact trace.step 6 (by decide)

theorem reordered_same_endpoint : reorderedTrace.state 7 = trace.state 7 := rfl

theorem reordered_roots_first (r t : Nat) (rootBound : r < 7) (stepBound : t < 7)
    (root : reorderedTrace.rule r = .insert)
    (lifecycle : ¬ External (reorderedTrace.rule t)) : r < t := by
  have rootIndices : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  have stepIndices : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
  rcases rootIndices with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases stepIndices with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [reorderedTrace, External]

end
end Cordis.CanonicalOrderCounterexample
