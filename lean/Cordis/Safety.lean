import Cordis.Stages

/-! Registry parent and table ownership invariants for the nine rules.
Both L-Divert alternatives use their concrete stage semantics. -/
namespace Cordis.Safety
open Calculus Stages
universe u
variable {Name Key Value Code Error : Type u}
local notation "R" => Registry Name Key Value Code (Inverse Name Key Value) Error
local notation "F" => Fiber Name Key Value Code (Inverse Name Key Value) Error
variable [DecidableEq Name] [DecidableEq Key]

def ParentClosed (r : R) : Prop :=
  ∀ child fiber parent, r child = some fiber → fiber.parent = some parent → r parent ≠ none

omit [DecidableEq Name] [DecidableEq Key] in
theorem empty_parentClosed : ParentClosed (fun _ => none : R) := by
  intro child fiber parent present
  contradiction

omit [DecidableEq Key] in
private theorem put_presence (r : R) (name other : Name) (fiber : F)
    (present : r other ≠ none) : put r name fiber other ≠ none := by
  by_cases same : other = name <;> simp [put, same, present]

omit [DecidableEq Key] in
theorem put_parentClosed (r : R) (name : Name) (fiber : F) (closed : ParentClosed r)
    (validParent : ∀ parent, fiber.parent = some parent → r parent ≠ none) :
    ParentClosed (put r name fiber) := by
  intro child entry parent present parentOf
  by_cases same : child = name
  · subst child
    have eq : fiber = entry := Option.some.inj (by simpa [put] using present)
    subst entry
    exact put_presence r name parent fiber (validParent parent parentOf)
  · have old : r child = some entry := by simpa [put, same] using present
    exact put_presence r name parent fiber (closed child entry parent old parentOf)

omit [DecidableEq Key] in
private theorem modify_eq_put (r : R) (name : Name) (fiber : F) (change : F → F)
    (present : r name = some fiber) :
    Calculus.modify r name change = put r name (change fiber) := by
  funext other
  by_cases same : other = name
  · subst other; simp [Calculus.modify, put, present]
  · simp [Calculus.modify, put, same]

omit [DecidableEq Key] in
theorem modify_parentClosed (r : R) (name : Name) (change : F → F)
    (sameParent : ∀ fiber, (change fiber).parent = fiber.parent) (closed : ParentClosed r) :
    ParentClosed (Calculus.modify r name change) := by
  cases present : r name with
  | none =>
    have unchanged : Calculus.modify r name change = r := by
      funext other
      by_cases same : other = name
      · subst other; simp [Calculus.modify, present]
      · simp [Calculus.modify, same]
    rw [unchanged]
    exact closed
  | some fiber =>
    rw [modify_eq_put r name fiber change present]
    apply put_parentClosed r name (change fiber) closed
    intro parent parentOf
    rw [sameParent] at parentOf
    exact closed name fiber parent present parentOf

omit [DecidableEq Key] in
theorem mark_parentClosed (r : R) (name : Name) (phase)
    (closed : ParentClosed r) : ParentClosed (mark r name phase) :=
  modify_parentClosed r name _ (fun _ => rfl) closed

omit [DecidableEq Key] in
theorem retire_parentClosed (r : R) (name : Name)
    (closed : ParentClosed r) : ParentClosed (Calculus.retire r name) :=
  modify_parentClosed r name _ (fun _ => rfl) closed

omit [DecidableEq Key] in
theorem remove_parentClosed (r : R) (name : Name) (closed : ParentClosed r)
    (ready : Removable r name) : ParentClosed (erase r name) := by
  intro child fiber parent present parentOf
  have childDifferent : child ≠ name := by
    intro same
    simp [erase, same] at present
  have old : r child = some fiber := by simpa [erase, childDifferent] using present
  have parentDifferent : parent ≠ name := by
    intro same
    subst parent
    exact child_prevents_removal r name child fiber old parentOf ready
  simpa [erase, parentDifferent] using closed child fiber parent old parentOf

theorem write_parentClosed (r : R) (name : Name) (key : Key) (value : Option Value)
    (closed : ParentClosed r) : ParentClosed (write r name key value) :=
  modify_parentClosed r name _ (fun _ => rfl) closed

theorem undo_parentClosed (r : R) (inverse : Inverse Name Key Value)
    (closed : ParentClosed r) : ParentClosed (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact closed
  | restrict name key => exact write_parentClosed r name key none closed
  | operate name key inverse => exact modify_parentClosed r name _ (fun _ => rfl) closed
  | retire child => exact retire_parentClosed r child closed

theorem discharge_parentClosed (r : R) (accumulator : List (Inverse Name Key Value))
    (closed : ParentClosed r) : ParentClosed (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact closed
  | cons inverse rest ih => exact ih (Stages.undo inverse r) (undo_parentClosed r inverse closed)

theorem landing_parentClosed (program : Code → Instruction Name Key Value Code Error)
    {name : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program name code r s inverse next) (closed : ParentClosed r) :
    ParentClosed s := by
  cases landing with
  | unit => exact closed
  | provide r name code fiber key value _ _ _ _ =>
    exact write_parentClosed r name key (some value) closed
  | operate r name code key run owner before after inverse result _ _ _ =>
    exact write_parentClosed r owner key (some after) closed
  | instantiate r name code component child _ allowed =>
    apply put_parentClosed r child (fresh component (some name)) closed
    exact allowed.2.1

/-- Parent closure is preserved by every one of the nine paper rules, with the
actual landed effects and actual accumulated inverses included. -/
theorem step_parentClosed (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s) (closed : ParentClosed r) :
    ParentClosed s := by
  cases step with
  | insert name component parent allowed =>
    exact put_parentClosed r name (fresh component parent) closed allowed.2.1
  | retire name _ => exact retire_parentClosed r name closed
  | remove name ready => exact remove_parentClosed r name closed ready
  | begin name fiber view _ _ _ _ => exact mark_parentClosed r name _ closed
  | iter s name fiber code accumulator view inverse next _ _ _ landing =>
    exact mark_parentClosed s name _ (landing_parentClosed program landing closed)
  | finish s name fiber code accumulator view inverse _ _ _ landing =>
    exact mark_parentClosed s name _ (landing_parentClosed program landing closed)
  | divert s name fiber code accumulator view tail _ _ _ alternative =>
    apply mark_parentClosed s name _
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, landing, _⟩
    · simpa [same] using closed
    · exact landing_parentClosed program landing closed
  | leave name fiber accumulator view _ _ _ => exact mark_parentClosed r name _ closed
  | unload name fiber accumulator view _ _ _ =>
    exact mark_parentClosed _ name _ (discharge_parentClosed r accumulator closed)

/-- Every binding is owned by a declaration of its provider (Definition 48).
This does not require that every declared provision is actually published. -/
def Owned (r : R) : Prop :=
  ∀ name fiber key, r name = some fiber → fiber.table key ≠ none → fiber.component.provides key

omit [DecidableEq Name] [DecidableEq Key] in
theorem empty_owned : Owned (fun _ => none : R) := by
  intro name fiber key present
  contradiction

omit [DecidableEq Key] in
theorem put_owned (r : R) (name : Name) (fiber : F) (owned : Owned r)
    (own : ∀ key, fiber.table key ≠ none → fiber.component.provides key) :
    Owned (put r name fiber) := by
  intro other entry key present bound
  by_cases same : other = name
  · subst other
    have eq : fiber = entry := Option.some.inj (by simpa [put] using present)
    subst entry
    exact own key bound
  · exact owned other entry key (by simpa [put, same] using present) bound

omit [DecidableEq Key] in
theorem modify_owned (r : R) (name : Name) (change : F → F) (owned : Owned r)
    (safe : ∀ fiber, r name = some fiber →
      (∀ key, fiber.table key ≠ none → fiber.component.provides key) →
      ∀ key, (change fiber).table key ≠ none → (change fiber).component.provides key) :
    Owned (Calculus.modify r name change) := by
  cases present : r name with
  | none =>
    have unchanged : Calculus.modify r name change = r := by
      funext other
      by_cases same : other = name
      · subst other; simp [Calculus.modify, present]
      · simp [Calculus.modify, same]
    rw [unchanged]
    exact owned
  | some fiber =>
    rw [modify_eq_put r name fiber change present]
    exact put_owned r name (change fiber) owned
      (safe fiber present (fun key bound => owned name fiber key present bound))

omit [DecidableEq Key] in
theorem mark_owned (r : R) (name : Name) (phase) (owned : Owned r) :
    Owned (mark r name phase) :=
  modify_owned r name _ owned (fun _ _ old => old)

omit [DecidableEq Key] in
theorem retire_owned (r : R) (name : Name) (owned : Owned r) :
    Owned (Calculus.retire r name) :=
  modify_owned r name _ owned (fun _ _ old => old)

omit [DecidableEq Key] in
theorem erase_owned (r : R) (name : Name) (owned : Owned r) : Owned (erase r name) := by
  intro other fiber key present bound
  by_cases same : other = name
  · simp [erase, same] at present
  · exact owned other fiber key (by simpa [erase, same] using present) bound

theorem write_owned (r : R) (name : Name) (key : Key) (value : Option Value)
    (owned : Owned r)
    (allowed : ∀ fiber, r name = some fiber → value ≠ none → fiber.component.provides key) :
    Owned (write r name key value) := by
  apply modify_owned r name _ owned
  intro fiber present old other bound
  by_cases same : other = key
  · subst other
    exact allowed fiber present (by simpa using bound)
  · exact old other (by simpa [same] using bound)

theorem undo_owned (r : R) (inverse : Inverse Name Key Value) (owned : Owned r) :
    Owned (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact owned
  | restrict name key =>
    exact write_owned r name key none owned (fun _ _ impossible => False.elim (impossible rfl))
  | operate name key inverse =>
    apply modify_owned r name _ owned
    intro fiber present old other bound
    by_cases same : other = key
    · subst other
      apply old key
      intro absent
      simp [absent] at bound
    · exact old other (by simpa [same] using bound)
  | retire child => exact retire_owned r child owned

theorem discharge_owned (r : R) (accumulator : List (Inverse Name Key Value))
    (owned : Owned r) : Owned (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact owned
  | cons inverse rest ih => exact ih (Stages.undo inverse r) (undo_owned r inverse owned)

omit [DecidableEq Name] [DecidableEq Key] in
/-- Resolving an operation proves that its target is an existing retained binding. -/
theorem location_binding (r : R) (name owner : Name) (key : Key) (value : Value)
    (located : location r name key = some (owner, value)) :
    ∃ fiber, r owner = some fiber ∧ fiber.table key = some value := by
  obtain ⟨selected, _, result⟩ := Option.bind_eq_some_iff.mp located
  obtain ⟨bound, lookup, pair⟩ := Option.map_eq_some_iff.mp result
  cases pair
  obtain ⟨fiber, present, binding⟩ := Option.bind_eq_some_iff.mp lookup
  exact ⟨fiber, present, binding⟩

theorem landing_owned (program : Code → Instruction Name Key Value Code Error)
    {name : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program name code r s inverse next) (owned : Owned r) : Owned s := by
  cases landing with
  | unit => exact owned
  | provide r name code fiber key value _ present allowed _ =>
    apply write_owned r name key (some value) owned
    intro entry entryPresent _
    have eq : entry = fiber := Option.some.inj (entryPresent.symm.trans present)
    simpa [eq] using allowed
  | operate r name code key run owner before after inverse result _ located _ =>
    obtain ⟨fiber, present, bound⟩ := location_binding r name owner key before located
    apply write_owned r owner key (some after) owned
    intro entry entryPresent _
    have eq : entry = fiber := Option.some.inj (entryPresent.symm.trans present)
    subst entry
    exact owned owner fiber key present (by simp [bound])
  | instantiate r name code component child _ _ =>
    exact put_owned r child (fresh component (some name)) owned
      (fun _ impossible => False.elim (impossible rfl))

/-- All nine rules preserve declaration ownership, including shared coeffect
operations and the actual inverse accumulator. Arbitrary value inverses may fail
their recovery law; they still cannot introduce an undeclared binding here. -/
theorem step_owned (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s) (owned : Owned r) : Owned s := by
  cases step with
  | insert name component parent _ =>
    exact put_owned r name (fresh component parent) owned
      (fun _ impossible => False.elim (impossible rfl))
  | retire name _ => exact retire_owned r name owned
  | remove name _ => exact erase_owned r name owned
  | begin name fiber view _ _ _ _ => exact mark_owned r name _ owned
  | iter s name fiber code accumulator view inverse next _ _ _ landing =>
    exact mark_owned s name _ (landing_owned program landing owned)
  | finish s name fiber code accumulator view inverse _ _ _ landing =>
    exact mark_owned s name _ (landing_owned program landing owned)
  | divert s name fiber code accumulator view tail _ _ _ alternative =>
    apply mark_owned s name _
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, landing, _⟩
    · simpa [same] using owned
    · exact landing_owned program landing owned
  | leave name fiber accumulator view _ _ _ => exact mark_owned r name _ owned
  | unload name fiber accumulator view _ _ _ =>
    exact mark_owned _ name _ (discharge_owned r accumulator owned)

/-- A strict natural-number rank along parent edges rules out cycles. Every fiber
has one optional parent by representation; parent closure then makes a rooted tree. -/
def Ranked (r : R) (rank : Name → Nat) : Prop :=
  ∀ child fiber parent, r child = some fiber → fiber.parent = some parent → rank parent < rank child

def Tree (r : R) : Prop := ParentClosed r ∧ ∃ rank, Ranked r rank

omit [DecidableEq Name] [DecidableEq Key] in
theorem empty_tree : Tree (fun _ => none : R) := by
  refine ⟨empty_parentClosed, fun _ => 0, ?_⟩
  intro child fiber parent present
  contradiction

omit [DecidableEq Key] in
private theorem put_ranked (r : R) (name : Name) (fiber : F) (rank : Name → Nat)
    (ranked : Ranked r rank) (own : ∀ parent, fiber.parent = some parent → rank parent < rank name) :
    Ranked (put r name fiber) rank := by
  intro child entry parent present parentOf
  by_cases same : child = name
  · subst child
    have eq : fiber = entry := Option.some.inj (by simpa [put] using present)
    subst entry
    exact own parent parentOf
  · exact ranked child entry parent (by simpa [put, same] using present) parentOf

omit [DecidableEq Key] in
theorem modify_ranked (r : R) (name : Name) (change : F → F) (rank : Name → Nat)
    (sameParent : ∀ fiber, (change fiber).parent = fiber.parent) (ranked : Ranked r rank) :
    Ranked (Calculus.modify r name change) rank := by
  cases present : r name with
  | none =>
    have unchanged : Calculus.modify r name change = r := by
      funext other
      by_cases same : other = name
      · subst other; simp [Calculus.modify, present]
      · simp [Calculus.modify, same]
    rw [unchanged]
    exact ranked
  | some fiber =>
    rw [modify_eq_put r name fiber change present]
    apply put_ranked r name (change fiber) rank ranked
    intro parent parentOf
    rw [sameParent] at parentOf
    exact ranked name fiber parent present parentOf

omit [DecidableEq Key] in
theorem modify_tree (r : R) (name : Name) (change : F → F)
    (sameParent : ∀ fiber, (change fiber).parent = fiber.parent) (tree : Tree r) :
    Tree (Calculus.modify r name change) := by
  obtain ⟨closed, rank, ranked⟩ := tree
  exact ⟨modify_parentClosed r name change sameParent closed,
    rank, modify_ranked r name change rank sameParent ranked⟩

omit [DecidableEq Key] in
theorem insert_tree (r : R) (name : Name) (component : Component Key Code) (parent : Option Name)
    (tree : Tree r) (allowed : Insertable r name component parent) :
    Tree (put r name (fresh component parent)) := by
  obtain ⟨closed, rank, ranked⟩ := tree
  refine ⟨put_parentClosed r name (fresh component parent) closed allowed.2.1, ?_⟩
  let nextRank : Name → Nat := fun other =>
    if other = name then (parent.map (fun p => rank p + 1)).getD 0 else rank other
  refine ⟨nextRank, ?_⟩
  intro child entry p present parentOf
  by_cases same : child = name
  · subst child
    have eq : fresh component parent = entry := Option.some.inj (by simpa [put] using present)
    subst entry
    have parentEq : parent = some p := parentOf
    have different : p ≠ name := by
      intro same
      exact allowed.2.1 p parentEq (by simpa [same] using allowed.1)
    simp [nextRank, different, parentEq]
  · have old : r child = some entry := by simpa [put, same] using present
    have parentDifferent : p ≠ name := by
      intro same
      exact closed child entry p old parentOf (by simpa [same] using allowed.1)
    simpa [nextRank, same, parentDifferent] using ranked child entry p old parentOf

omit [DecidableEq Key] in
theorem remove_tree (r : R) (name : Name) (tree : Tree r) (ready : Removable r name) :
    Tree (erase r name) := by
  obtain ⟨closed, rank, ranked⟩ := tree
  refine ⟨remove_parentClosed r name closed ready, rank, ?_⟩
  intro child fiber parent present parentOf
  by_cases same : child = name
  · simp [erase, same] at present
  · exact ranked child fiber parent (by simpa [erase, same] using present) parentOf

theorem undo_tree (r : R) (inverse : Inverse Name Key Value) (tree : Tree r) :
    Tree (Stages.undo inverse r) := by
  cases inverse with
  | unit => exact tree
  | restrict name key => exact modify_tree r name _ (fun _ => rfl) tree
  | operate name key inverse => exact modify_tree r name _ (fun _ => rfl) tree
  | retire child => exact modify_tree r child _ (fun _ => rfl) tree

theorem discharge_tree (r : R) (accumulator : List (Inverse Name Key Value)) (tree : Tree r) :
    Tree (discharge Stages.undo accumulator r) := by
  induction accumulator generalizing r with
  | nil => exact tree
  | cons inverse rest ih => exact ih (Stages.undo inverse r) (undo_tree r inverse tree)

theorem landing_tree (program : Code → Instruction Name Key Value Code Error)
    {name : Name} {code : Code} {r s : R} {inverse : Inverse Name Key Value} {next : Option Code}
    (landing : Land program name code r s inverse next) (tree : Tree r) : Tree s := by
  cases landing with
  | unit => exact tree
  | provide r name code fiber key value _ _ _ _ =>
    exact modify_tree r name _ (fun _ => rfl) tree
  | operate r name code key run owner before after inverse result _ _ _ =>
    exact modify_tree r owner _ (fun _ => rfl) tree
  | instantiate r name code component child _ allowed =>
    exact insert_tree r child component (some name) tree allowed

/-- All nine rules preserve both parent closure and a strict parent-edge ranking.
This proves an actual tree property, rather than just absence of dangling names. -/
theorem step_tree (program : Code → Instruction Name Key Value Code Error)
    {r s : R} (step : Step (Land program) Stages.undo r s) (tree : Tree r) : Tree s := by
  cases step with
  | insert name component parent allowed => exact insert_tree r name component parent tree allowed
  | retire name _ => exact modify_tree r name _ (fun _ => rfl) tree
  | remove name ready => exact remove_tree r name tree ready
  | begin name fiber view _ _ _ _ => exact modify_tree r name _ (fun _ => rfl) tree
  | iter s name fiber code accumulator view inverse next _ _ _ landing =>
    exact modify_tree s name _ (fun _ => rfl) (landing_tree program landing tree)
  | finish s name fiber code accumulator view inverse _ _ _ landing =>
    exact modify_tree s name _ (fun _ => rfl) (landing_tree program landing tree)
  | divert s name fiber code accumulator view tail _ _ _ alternative =>
    unfold mark
    apply modify_tree s name (fun fiber => { fiber with phase := .unloading (tail ++ accumulator) view }) (fun _ => rfl)
    rcases alternative with ⟨same, _⟩ | ⟨inverse, next, landing, _⟩
    · simpa [same] using tree
    · exact landing_tree program landing tree
  | leave name fiber accumulator view _ _ _ => exact modify_tree r name _ (fun _ => rfl) tree
  | unload name fiber accumulator view _ _ _ =>
    exact modify_tree _ name _ (fun _ => rfl) (discharge_tree r accumulator tree)

end Cordis.Safety
