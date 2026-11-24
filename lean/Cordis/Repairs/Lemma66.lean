import Cordis.Repairs.ScopedAdmissionExchange
import Cordis.Repairs.GuardedIteratorProvenance
import Cordis.PaperRemainingClaims

/-! Lemma 66 on common admitted probes, with the selected reservations
of its generated maps and the original historical component quantification. -/
namespace Cordis.Repairs.Lemma66
open TypedRegistry MediatedAdmission
open ScopedIteratorObservation ScopedIteratorGenerators ScopedAdmissionExchange
open PairwiseNativeWords
open PairwiseMixed (controlPart StampedRelated)
open PaperEffectEquations (CoeffectOperations)
open PartialCoeffectIndependenceContracts (tableSetoid)
open PaperRemainingClaims (DeclaresInto)
open Iterators (OptionRel)

universe u
variable {Name Key Code : Type u} {V : Key → Type u}
variable [DecidableEq Name] [DecidableEq Key] {ops : CoeffectOperations V}
variable {program : Code → Instruction Name ops Code}
variable {observe : ∀ key, Setoid (V key)}
variable {actor foreignActor : Name} {component foreignComponent : Calculus.Component Key Code}
local notation "SR" => PairwiseControl.Stamped Name V Code
local notation "N" => Node program actor observe (Interface component)

private noncomputable def entry (choices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component component.entry) : N :=
  Node.compiled (recipe (actor := actor) choices lawful grammar [])

/-- Both entries' chosen words are admitted from this probe, with the
reservation checks for their selected calculations. -/
structure EntryProbe (choices foreignChoices : Choices ops Name Code) (lawful : OperationsLawful ops observe)
    {grammar : Mediated program component component.entry}
    {foreignGrammar : Mediated program foreignComponent foreignComponent.entry}
    {script : List (Letter program actor)} {foreign : List (Letter program foreignActor)}
    (word : Word (entry (actor := actor) choices lawful grammar) script)
    (otherWord : Word (entry (actor := foreignActor) foreignChoices lawful foreignGrammar) foreign)
    (probe : SR) : Prop where
  acting : ∃ row, probe.1 actor = some row ∧ row.component = component
  foreignActing : ∃ row, probe.1 foreignActor = some row ∧ row.component = foreignComponent
  localScope : word.Admitted probe
  foreignScope : otherWord.Admitted probe
  reservations : WordReservations choices lawful word probe (controlPart (words foreign))
  foreignReservations : WordReservations foreignChoices lawful otherWord probe (controlPart (words script))
  self : StampedRelated ops observe probe probe

/-- The two orders are compared at any two table-related probes admitted
by both words. The option observation includes genuine failure. -/
def EntriesCommute (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component component.entry)
    (foreignGrammar : Mediated program foreignComponent foreignComponent.entry)
    (actor foreignActor : Name) : Prop :=
  ∀ (choices foreignChoices : Choices ops Name Code)
    {script : List (Letter program actor)} {foreign : List (Letter program foreignActor)}
    (word : Word (entry (actor := actor) choices lawful grammar) script)
    (otherWord : Word (entry (actor := foreignActor) foreignChoices lawful foreignGrammar) foreign)
    {first second : SR},
    (∀ edit ∈ controlPart (words script), ∀ other ∈ controlPart (words foreign),
      PairwiseControl.Compatible edit other) →
    EntryProbe choices foreignChoices lawful word otherWord first →
    EntryProbe choices foreignChoices lawful word otherWord second →
    TypedStateObservation.TablesRelatedAt observe (fun _ => True) first.1 second.1 →
    OptionRel (fun left right : SR =>
      TypedStateObservation.TablesRelatedAt observe (fun _ => True) left.1 right.1)
      ((otherWord.run first).bind word.run) ((word.run second).bind otherWord.run)

/-- Every successful foreign word preserves the yielded inverse and
continuation at each reachable head, with birth payloads compared too. -/
def EntryYields (lawful : OperationsLawful ops observe)
    (grammar : Mediated program component component.entry)
    (foreignGrammar : Mediated program foreignComponent foreignComponent.entry)
    (actor foreignActor : Name) : Prop :=
  ∀ (choices foreignChoices : Choices ops Name Code)
    {node : Node program actor observe (Interface component)}
    (reached : Reach (entry (actor := actor) choices lawful grammar) node)
    (head : Forward program actor node.code) (drawn : head.draw = node.draw)
    {foreign : List (Letter program foreignActor)}
    (otherWord : Word (entry (actor := foreignActor) foreignChoices lawful foreignGrammar) foreign)
    {before after : SR} {otherRow : Fiber Name V Code},
    before.1 foreignActor = some otherRow → otherRow.component = foreignComponent →
    otherWord.run before = some after →
    ∀ (admitted : node.domain before.1), head.ready before.1 →
      GeneratorReservations choices lawful (.advance node reached head drawn) before.1 (controlPart (words foreign)) →
      StampedRelated ops observe before before →
      ∃ moved : node.domain after.1,
        OptionRel YieldPreserved (node.evaluate ⟨before.1, admitted⟩) (node.evaluate ⟨after.1, moved⟩)

private theorem entry_yields (lawful : OperationsLawful ops observe)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (grammar : Mediated program component component.entry)
    (foreignGrammar : Mediated program foreignComponent foreignComponent.entry) :
    EntryYields lawful grammar foreignGrammar actor foreignActor := by
  intro choices foreignChoices node reached head drawn foreign otherWord before after otherRow
    found payload foreignRun admitted ready reservations initial
  obtain ⟨_, _, path⟩ := otherWord.run_iff.mp foreignRun
  have origins := word_origins foreignChoices lawful otherWord
  have otherReady := path.ready found
  have allowed := script_admitted foreign found payload otherReady origins
  have self := PairwiseMixed.mixed_respects ops observe laws (words foreign) allowed initial
  rw [path.record] at self
  exact generator_yield_after_word choices lawful laws respect different separate reached head drawn
    ⟨otherRow, found, payload⟩ foreign otherReady origins initial path.record self admitted ready reservations

private theorem entries_commute (lawful : OperationsLawful ops observe)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    (different : actor ≠ foreignActor) (separate : Transposition.Separated component foreignComponent)
    (grammar : Mediated program component component.entry)
    (foreignGrammar : Mediated program foreignComponent foreignComponent.entry) :
    EntriesCommute lawful grammar foreignGrammar actor foreignActor := by
  intro choices foreignChoices script foreign word otherWord first second births left right observed
  let tableOnly := fun a b : SR => TypedStateObservation.TablesRelatedAt observe (fun _ => True) a.1 b.1
  have movedScope {before after : SR} (probe : EntryProbe choices foreignChoices lawful word otherWord before)
      (called : otherWord.run before = some after) : word.Admitted after := by
    obtain ⟨_, _, native⟩ := otherWord.run_iff.mp called
    obtain ⟨row, found, payload⟩ := probe.foreignActing
    exact (word_after_native_path choices lawful laws respect different separate word
      (word_origins foreignChoices lawful otherWord) births probe.acting found payload probe.self native
      probe.localScope probe.reservations).1
  have sameOrder : OptionRel tableOnly ((otherWord.run first).bind word.run) ((otherWord.run second).bind word.run) := by
    have outer := word_respects_tables foreignChoices lawful otherWord left.foreignScope right.foreignScope observed
    cases firstCall : otherWord.run first <;> cases secondCall : otherWord.run second <;>
      simp only [firstCall, secondCall, Option.bind_none, Option.bind_some, OptionRel] at outer ⊢
    exact word_respects_tables choices lawful word (movedScope left firstCall) (movedScope right secondCall) outer
  obtain ⟨leftRow, leftFound, leftPayload⟩ := right.acting
  obtain ⟨rightRow, rightFound, rightPayload⟩ := right.foreignActing
  have secondOrder := compiled_partial_words_commute observe laws respect lawful grammar foreignGrammar choices foreignChoices
    [] [] word otherWord different separate leftFound leftPayload rightFound rightPayload right.localScope
    right.foreignScope births right.reservations right.foreignReservations right.self
  apply OptionRel.trans (R := tableOnly) (fun _ _ _ earlier later => earlier.trans later) sameOrder
  apply OptionRel.mono (fun first second relation => ?_) secondOrder
  letI : Setoid (Scalar ops) := TypedCoeffectReplay.setoid observe
  apply (TypedStateObservation.tables_related_encode_iff ops observe (fun _ => True) _ _).mp
  exact PaperStateObservation.tables_of_homogeneous (relation.2.tables.projected (fun _ => True))
    (fun _ _ _ same => same)

omit [DecidableEq Name] [DecidableEq Key] in
theorem separated_or_overlap (left right : Calculus.Component Key Code) :
    Transposition.Separated left right ∨ DeclaresInto left right ∨ DeclaresInto right left := by
  classical
  by_cases overlap : DeclaresInto left right ∨ DeclaresInto right left
  · exact .inr overlap
  · refine .inl ⟨?_, ?_, ?_⟩
    · intro key provided
      cases other : right.provides key
      · rfl
      · exact False.elim (overlap (.inl ⟨key, provided, .inr other⟩))
    · intro key provided
      cases other : right.requires key
      · rfl
      · exact False.elim (overlap (.inl ⟨key, provided, .inl other⟩))
    · intro key provided
      cases other : left.requires key
      · rfl
      · exact False.elim (overlap (.inr ⟨key, provided, .inl other⟩))

/-- Historical pairs include entries that never coexist in the observed
trace. Both inherit their grammar from their actual births. For a
separated pair the independence clauses apply on common admitted probes
under the selected scope and birth checks. The overlapping pair retains
the original commutative-key conclusion. -/
theorem lemma66_scoped (lawful : OperationsLawful ops observe)
    (laws : ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key)
    (respect : ∀ key, PaperObservationEquations.OperationRespects ops key (observe key).r)
    {last leftTime rightTime : Nat}
    (trace : GuardedHistory.Trace (encodeProgram program) last)
    (admitted : GuardedIteratorProvenance.BirthsMediated trace)
    (leftIn : leftTime ≤ last) (rightIn : rightTime ≤ last)
    {leftActor rightActor : Name} (different : leftActor ≠ rightActor)
    {leftRow rightRow : RawFiber Name ops Code}
    (leftFound : trace.state leftTime leftActor = some leftRow)
    (rightFound : trace.state rightTime rightActor = some rightRow) :
    ∃ (leftGrammar : Mediated program leftRow.component leftRow.component.entry)
      (rightGrammar : Mediated program rightRow.component rightRow.component.entry),
      (EntriesCommute lawful leftGrammar rightGrammar leftActor rightActor ∧
        EntryYields lawful leftGrammar rightGrammar leftActor rightActor ∧
        EntryYields lawful rightGrammar leftGrammar rightActor leftActor) ∨
      ((DeclaresInto leftRow.component rightRow.component ∨ DeclaresInto rightRow.component leftRow.component) ∧
        ∀ key, PaperObservationEquations.CommutativeKey ops (tableSetoid observe (fun _ => True)) key) := by
  have leftGrammar : Mediated program leftRow.component leftRow.component.entry :=
    (GuardedIteratorProvenance.codes_at_cut trace admitted leftTime leftIn).1 leftActor leftRow leftFound
  have rightGrammar : Mediated program rightRow.component rightRow.component.entry :=
    (GuardedIteratorProvenance.codes_at_cut trace admitted rightTime rightIn).1 rightActor rightRow rightFound
  refine ⟨leftGrammar, rightGrammar, ?_⟩
  rcases separated_or_overlap leftRow.component rightRow.component with separated | overlap
  · exact .inl ⟨entries_commute lawful laws respect different separated leftGrammar rightGrammar,
      entry_yields lawful laws respect different separated leftGrammar rightGrammar,
      entry_yields lawful laws respect different.symm separated.symm rightGrammar leftGrammar⟩
  · exact .inr ⟨overlap, laws⟩

end Cordis.Repairs.Lemma66
