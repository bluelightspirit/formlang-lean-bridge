import Std

/-!
  Formal finite-automata semantics.

  State subsets are represented by duplicate-free lists.
  This module does not depend on Mathlib.
-/

namespace FormalAutomata

/-- A nondeterministic finite automaton. -/
structure NFA (Q α : Type) where
  states : List Q
  alphabet : List α
  initial : List Q
  accepting : List Q
  transition : Q → α → List Q

namespace NFA

variable {Q α : Type} [DecidableEq Q]

/-- All destinations reachable from a set of states on one symbol. -/
def step (A : NFA Q α) (current : List Q) (symbol : α) : List Q :=
  (current.flatMap fun q => A.transition q symbol).eraseDups

/-- States reachable after processing a complete word. -/
def run (A : NFA Q α) (word : List α) : List Q :=
  word.foldl (fun current symbol => A.step current symbol)
    A.initial.eraseDups

/-- NFA acceptance: at least one reachable state is accepting. -/
def accepts (A : NFA Q α) (word : List α) : Bool :=
  (A.run word).any fun q => A.accepting.contains q

end NFA

/-- A deterministic finite automaton. -/
structure DFA (S α : Type) where
  initial : S
  transition : S → α → S
  accepting : S → Bool

namespace DFA

/-- Process a word using the deterministic transition function. -/
def run {S α : Type} (A : DFA S α) (word : List α) : S :=
  word.foldl (fun current symbol => A.transition current symbol) A.initial

/-- DFA acceptance. -/
def accepts {S α : Type} (A : DFA S α) (word : List α) : Bool :=
  A.accepting (A.run word)

end DFA

variable {Q α : Type} [DecidableEq Q]

/--
  Subset construction.

  A state of the resulting DFA is a list representing a subset
  of the original NFA's states.
-/
def subsetDFA (A : NFA Q α) : DFA (List Q) α where
  initial := A.initial.eraseDups
  transition := A.step
  accepting := fun subset =>
    subset.any fun q => A.accepting.contains q

/-- The subset DFA uses exactly the NFA's set-valued step function. -/
theorem subset_step_correct
    (A : NFA Q α) (current : List Q) (symbol : α) :
    (subsetDFA A).transition current symbol = A.step current symbol := by
  rfl

/--
  Main theorem: subset construction preserves acceptance.

  For every word, the resulting DFA and original NFA
  return the same acceptance result.
-/
theorem subset_construction_preserves_acceptance
    (A : NFA Q α) (word : List α) :
    DFA.accepts (subsetDFA A) word = NFA.accepts A word := by
  rfl

/-- A useful corollary: both automata agree on rejection as well. -/
theorem subset_construction_preserves_rejection
    (A : NFA Q α) (word : List α) :
    DFA.accepts (subsetDFA A) word = false ↔
    NFA.accepts A word = false := by
  rw [subset_construction_preserves_acceptance]

end FormalAutomata

namespace FormalAutomata.PathProof

/-- An NFA described by initial states, accepting states, and transitions. -/
structure NFA (Q α : Type) where
  initial : List Q
  accepting : List Q
  transition : Q → α → List Q

/-- A valid path through an NFA, independent of its execution function. -/
inductive Path (A : NFA Q α) : Q → List α → Q → Prop
  | nil (q : Q) : Path A q [] q
  | cons {q q' r : Q} {a : α} {word : List α}
      (hstep : q' ∈ A.transition q a)
      (htail : Path A q' word r) :
      Path A q (a :: word) r

/-- All states reachable in one transition from a list of states. -/
def step [DecidableEq Q]
    (A : NFA Q α) (current : List Q) (a : α) : List Q :=
  (current.flatMap fun q => A.transition q a).eraseDups

/-- Execute a word recursively over a set of current states. -/
def runFrom [DecidableEq Q]
    (A : NFA Q α) (current : List Q) : List α → List Q
  | [] => current
  | a :: word => runFrom A (step A current a) word

/-- Membership in one-step reachability means there was a valid edge. -/
theorem mem_step [DecidableEq Q]
    (A : NFA Q α) (current : List Q) (a : α) (r : Q) :
    r ∈ step A current a ↔
      ∃ q, q ∈ current ∧ r ∈ A.transition q a := by
  simp [step]

/--
A state is in the recursively computed reachable set exactly when
there is a valid path to it from some state in the starting set.
-/
theorem mem_runFrom_iff [DecidableEq Q]
    (A : NFA Q α) (current : List Q)
    (word : List α) (r : Q) :
    r ∈ runFrom A current word ↔
      ∃ q, q ∈ current ∧ Path A q word r := by
  induction word generalizing current with
  | nil =>
      simp [runFrom]
      constructor
      · intro h
        exact ⟨r, h, Path.nil r⟩
      · rintro ⟨q, hq, hpath⟩
        cases hpath
        exact hq
  | cons a word ih =>
      simp only [runFrom]
      rw [ih]
      constructor
      · rintro ⟨qmid, hmid, htail⟩
        obtain ⟨q, hq, hedge⟩ :=
          (mem_step A current a qmid).mp hmid
        exact ⟨q, hq, Path.cons hedge htail⟩
      · rintro ⟨q, hq, hpath⟩
        cases hpath with
        | cons hedge htail =>
            exact ⟨_, (mem_step A current a _).mpr
              ⟨q, hq, hedge⟩, htail⟩

/-- Acceptance computed by subset-style execution. -/
def acceptsSubset [DecidableEq Q]
    (A : NFA Q α) (word : List α) : Bool :=
  (runFrom A A.initial.eraseDups word).any
    fun q => A.accepting.contains q

/-- Acceptance defined directly by the existence of an accepting path. -/
def acceptsPath
    (A : NFA Q α) (word : List α) : Prop :=
  ∃ qf, (∃ q₀, q₀ ∈ A.initial ∧ Path A q₀ word qf) ∧
    qf ∈ A.accepting

/--
The central result: subset-style execution accepts exactly those words
for which an accepting NFA path exists.
-/
theorem subset_execution_iff_accepting_path [DecidableEq Q]
    (A : NFA Q α) (word : List α) :
    acceptsSubset A word = true ↔ acceptsPath A word := by
  simp [acceptsSubset, acceptsPath, mem_runFrom_iff]

end FormalAutomata.PathProof

namespace FormalAutomata

/-- Convert the original NFA into the independent path-proof model. -/
def toPathNFA {Q α : Type} (A : NFA Q α) :
    PathProof.NFA Q α where
  initial := A.initial
  accepting := A.accepting
  transition := A.transition

/--
The original foldl-based execution and the recursive path-proof
execution produce identical reachable-state lists.
-/
theorem foldl_eq_runFrom [DecidableEq Q]
    (A : NFA Q α) (current : List Q) (word : List α) :
    word.foldl (fun states symbol => NFA.step A states symbol) current =
      PathProof.runFrom (toPathNFA A) current word := by
  induction word generalizing current with
  | nil => rfl
  | cons a word ih =>
      simp only [List.foldl_cons, PathProof.runFrom]
      exact ih (NFA.step A current a)

/--
The original NFA accepts exactly when an accepting path exists.
This connects the original executable model to the independent
relational semantics.
-/
theorem original_accepts_iff_accepting_path
    [DecidableEq Q] (A : NFA Q α) (word : List α) :
    NFA.accepts A word = true ↔
      PathProof.acceptsPath (toPathNFA A) word := by
  unfold NFA.accepts NFA.run
  rw [foldl_eq_runFrom]
  exact PathProof.subset_execution_iff_accepting_path
    (toPathNFA A) word

end FormalAutomata


namespace FormalAutomata

/--
The subset DFA and original NFA agree on acceptance.
This proof uses the path semantics rather than definitional equality.
-/
theorem subset_dfa_iff_accepting_path
    [DecidableEq Q] (A : NFA Q α) (word : List α) :
    DFA.accepts (subsetDFA A) word = true ↔
      PathProof.acceptsPath (toPathNFA A) word := by
  unfold DFA.accepts DFA.run subsetDFA
  rw [foldl_eq_runFrom]
  exact PathProof.subset_execution_iff_accepting_path
    (toPathNFA A) word

/--
The subset DFA and original NFA agree on acceptance.
The proof connects both Boolean computations through
the independent accepting-path semantics.
-/
theorem subset_construction_via_paths
    [DecidableEq Q] (A : NFA Q α) (word : List α) :
    DFA.accepts (subsetDFA A) word = NFA.accepts A word := by
  have hd := subset_dfa_iff_accepting_path A word
  have hn := original_accepts_iff_accepting_path A word
  cases d : DFA.accepts (subsetDFA A) word <;>
    cases n : NFA.accepts A word <;>
    simp_all

end FormalAutomata


namespace FormalAutomata

/-- Conditions required for an NFA to be well-formed. -/
def WellFormed {Q α : Type} (A : NFA Q α) : Prop :=
  (∀ q, q ∈ A.initial → q ∈ A.states) ∧
  (∀ q, q ∈ A.accepting → q ∈ A.states) ∧
  (∀ q a q',
    q ∈ A.states →
    a ∈ A.alphabet →
    q' ∈ A.transition q a →
    q' ∈ A.states)

/-- Every initial state of a well-formed NFA is declared. -/
theorem initial_states_valid
    {Q α : Type} (A : NFA Q α)
    (h : WellFormed A) :
    ∀ q, q ∈ A.initial → q ∈ A.states :=
  h.1

/-- Every accepting state of a well-formed NFA is declared. -/
theorem accepting_states_valid
    {Q α : Type} (A : NFA Q α)
    (h : WellFormed A) :
    ∀ q, q ∈ A.accepting → q ∈ A.states :=
  h.2.1

end FormalAutomata

namespace FormalAutomata

/-- One NFA step preserves membership in the declared states. -/
theorem step_states_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (current : List Q)
    (hcurrent : ∀ q, q ∈ current → q ∈ A.states)
    (a : α)
    (ha : a ∈ A.alphabet) :
    ∀ q, q ∈ NFA.step A current a → q ∈ A.states := by
  intro q hq
  simp only [NFA.step, List.mem_eraseDups] at hq
  obtain ⟨p, hp, htransition⟩ := List.mem_flatMap.mp hq
  exact hA.2.2 p a q (hcurrent p hp) ha htransition

end FormalAutomata

namespace FormalAutomata

/-- Running an NFA over valid alphabet symbols preserves valid states. -/
theorem path_runFrom_states_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (current : List Q)
    (hcurrent : ∀ q, q ∈ current → q ∈ A.states)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    ∀ q,
      q ∈ PathProof.runFrom (toPathNFA A) current word →
      q ∈ A.states := by
  induction word generalizing current with
  | nil =>
      intro q hq
      simpa [PathProof.runFrom] using hcurrent q hq
  | cons a word ih =>
      have hstep :
          ∀ q,
            q ∈ PathProof.step (toPathNFA A) current a →
            q ∈ A.states := by
        intro q hq
        have hq' : q ∈ NFA.step A current a := by
          simpa [PathProof.step, toPathNFA, NFA.step] using hq
        exact step_states_valid A hA current hcurrent a
          (hword a (by simp)) q hq'
      apply ih (PathProof.step (toPathNFA A) current a) hstep
      intro b hb
      exact hword b (by simp [hb])

end FormalAutomata

namespace FormalAutomata

/-- Running a well-formed NFA from its initial states
    over valid alphabet symbols preserves declared states. -/
theorem run_states_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    ∀ q, q ∈ NFA.run A word → q ∈ A.states := by
  have hinitial :
      ∀ q, q ∈ A.initial.eraseDups → q ∈ A.states := by
    intro q hq
    exact initial_states_valid A hA q (by simpa using hq)
  have hvalid := path_runFrom_states_valid
    A hA A.initial.eraseDups hinitial word hword
  have hrun := foldl_eq_runFrom A A.initial.eraseDups word
  intro q hq
  change q ∈
    word.foldl (fun states symbol => NFA.step A states symbol)
      A.initial.eraseDups at hq
  rw [hrun] at hq
  exact hvalid q hq

end FormalAutomata

namespace FormalAutomata

/-- A DFA is well-formed relative to declared states and alphabet. -/
def DFA.WellFormed
    {S α : Type}
    (A : DFA S α)
    (states : List S)
    (alphabet : List α) : Prop :=
  A.initial ∈ states ∧
  (∀ q a, q ∈ states → a ∈ alphabet →
    A.transition q a ∈ states)

/-- Folding DFA transitions preserves membership in declared states. -/
theorem DFA.foldl_states_valid
    {S α : Type}
    (A : DFA S α)
    (states : List S)
    (alphabet : List α)
    (hA : DFA.WellFormed A states alphabet)
    (current : S)
    (hcurrent : current ∈ states)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ alphabet) :
    word.foldl
      (fun current symbol => A.transition current symbol)
      current ∈ states := by
  induction word generalizing current with
  | nil =>
      simpa using hcurrent
  | cons a word ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact hA.2 current a hcurrent (hword a (by simp))
      · intro b hb
        exact hword b (by simp [hb])

/-- A well-formed DFA remains within its declared states after a run. -/
theorem DFA.run_states_valid
    {S α : Type}
    (A : DFA S α)
    (states : List S)
    (alphabet : List α)
    (hA : DFA.WellFormed A states alphabet)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ alphabet) :
    DFA.run A word ∈ states := by
  unfold DFA.run
  exact DFA.foldl_states_valid A states alphabet hA
    A.initial hA.1 word hword

end FormalAutomata

namespace FormalAutomata

/-- A subset-DFA state contains only declared NFA states. -/
def SubsetStateValid
    {Q α : Type}
    (A : NFA Q α)
    (subset : List Q) : Prop :=
  ∀ q, q ∈ subset → q ∈ A.states

/-- The initial subset contains only declared NFA states. -/
theorem subset_initial_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A) :
    SubsetStateValid A A.initial.eraseDups := by
  intro q hq
  exact initial_states_valid A hA q (by simpa using hq)

/-- A subset-DFA transition produces another valid subset. -/
theorem subset_transition_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (current : List Q)
    (hcurrent : SubsetStateValid A current)
    (a : α)
    (ha : a ∈ A.alphabet) :
    SubsetStateValid A ((subsetDFA A).transition current a) := by
  intro q hq
  exact step_states_valid A hA current hcurrent a ha q hq

/-- Repeated subset-DFA transitions preserve subset validity. -/
theorem subset_foldl_states_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (current : List Q)
    (hcurrent : SubsetStateValid A current)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    SubsetStateValid A
      (word.foldl
        (fun current symbol =>
          (subsetDFA A).transition current symbol)
        current) := by
  induction word generalizing current with
  | nil =>
      exact hcurrent
  | cons a word ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact subset_transition_valid A hA current hcurrent a
          (hword a (by simp))
      · intro b hb
        exact hword b (by simp [hb])

/-- Every subset-DFA state reached by a valid input word
    contains only declared NFA states. -/
theorem subset_run_states_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    SubsetStateValid A (DFA.run (subsetDFA A) word) := by
  unfold DFA.run
  exact subset_foldl_states_valid A hA
    A.initial.eraseDups (subset_initial_valid A hA)
    word hword

end FormalAutomata

namespace FormalAutomata

/-- DFA well-formedness relative to a state-validity predicate. -/
def DFA.WellFormedOn
    {S α : Type}
    (A : DFA S α)
    (Valid : S → Prop)
    (alphabet : List α) : Prop :=
  Valid A.initial ∧
  (∀ q a, Valid q → a ∈ alphabet →
    Valid (A.transition q a))

/-- The subset DFA is well-formed on valid NFA-state subsets. -/
theorem subset_dfa_wellformed_on
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A) :
    DFA.WellFormedOn (subsetDFA A)
      (SubsetStateValid A) A.alphabet := by
  constructor
  · exact subset_initial_valid A hA
  · intro q a hq ha
    exact subset_transition_valid A hA q hq a ha

end FormalAutomata

namespace FormalAutomata

/-- Enumerate all subsets of a finite list, preserving source order. -/
def allSubsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest =>
      let subsets := allSubsets rest
      subsets ++ subsets.map (a :: ·)

end FormalAutomata

namespace FormalAutomata

/-- Put a subset into the order used by the original state list. -/
def canonicalSubset [DecidableEq α]
    (states subset : List α) : List α :=
  states.filter (fun q => q ∈ subset)

/-- Every canonical subset occurs in the finite subset enumeration. -/
theorem canonicalSubset_mem_allSubsets
    [DecidableEq α]
    (states subset : List α) :
    canonicalSubset states subset ∈ allSubsets states := by
  induction states with
  | nil =>
      simp [canonicalSubset, allSubsets]
  | cons a rest ih =>
      simp only [canonicalSubset, List.filter_cons]
      split
      · change a :: canonicalSubset rest subset ∈
          allSubsets rest ++ (allSubsets rest).map (a :: ·)
        apply List.mem_append.mpr
        right
        apply List.mem_map.mpr
        exact ⟨canonicalSubset rest subset, ih, rfl⟩
      · change canonicalSubset rest subset ∈
          allSubsets rest ++ (allSubsets rest).map (a :: ·)
        exact List.mem_append.mpr (Or.inl ih)

end FormalAutomata

namespace FormalAutomata

/-- A subset DFA whose states are canonical lists of NFA states. -/
def finiteSubsetDFA
    [DecidableEq Q]
    (A : NFA Q α) : DFA (List Q) α where
  initial := canonicalSubset A.states A.initial
  transition := fun current symbol =>
    canonicalSubset A.states (NFA.step A current symbol)
  accepting := fun subset =>
    subset.any fun q => A.accepting.contains q

/-- The finite subset DFA starts in its enumerated state collection. -/
theorem finite_subset_initial_valid
    [DecidableEq Q]
    (A : NFA Q α) :
    (finiteSubsetDFA A).initial ∈ allSubsets A.states := by
  exact canonicalSubset_mem_allSubsets A.states A.initial

/-- Every transition of the finite subset DFA stays
    inside its enumerated state collection. -/
theorem finite_subset_transition_valid
    [DecidableEq Q]
    (A : NFA Q α)
    (current : List Q)
    (symbol : α) :
    (finiteSubsetDFA A).transition current symbol ∈
      allSubsets A.states := by
  exact canonicalSubset_mem_allSubsets A.states
    (NFA.step A current symbol)

/-- The finite subset DFA is well-formed relative to
    its enumerated subset-state collection. -/
theorem finite_subset_dfa_wellformed
    [DecidableEq Q]
    (A : NFA Q α) :
    DFA.WellFormed (finiteSubsetDFA A)
      (allSubsets A.states) A.alphabet := by
  constructor
  · exact finite_subset_initial_valid A
  · intro q a hq ha
    exact finite_subset_transition_valid A q a

end FormalAutomata

namespace FormalAutomata

/-- Membership in a canonical subset is membership
    in both the state collection and the original subset. -/
theorem mem_canonicalSubset
    [DecidableEq α]
    (states subset : List α)
    (q : α) :
    q ∈ canonicalSubset states subset ↔
      q ∈ states ∧ q ∈ subset := by
  simp [canonicalSubset]

end FormalAutomata

namespace FormalAutomata

/-- Membership in a canonicalized NFA transition result. -/
theorem mem_canonical_step
    [DecidableEq Q]
    (A : NFA Q α)
    (current : List Q)
    (symbol : α)
    (q : Q) :
    q ∈ canonicalSubset A.states
      (NFA.step A current symbol) ↔
    q ∈ A.states ∧
      ∃ p, p ∈ current ∧ q ∈ A.transition p symbol := by
  simp [canonicalSubset, NFA.step]

end FormalAutomata

namespace FormalAutomata

/-- A canonicalized subset transition represents the same
    valid destination states as the original NFA transition. -/
theorem finite_subset_transition_membership
    [DecidableEq Q]
    (A : NFA Q α)
    (currentSubset current : List Q)
    (hrel : ∀ p,
      p ∈ currentSubset ↔
        p ∈ A.states ∧ p ∈ current)
    (hcurrent : ∀ p, p ∈ current → p ∈ A.states)
    (symbol : α)
    (q : Q) :
    q ∈ canonicalSubset A.states
      (NFA.step A currentSubset symbol) ↔
    q ∈ A.states ∧ q ∈ NFA.step A current symbol := by
  rw [mem_canonical_step]
  constructor
  · rintro ⟨hq, p, hp, htransition⟩
    have hp' := (hrel p).mp hp
    constructor
    · exact hq
    · simpa [NFA.step] using
        (show ∃ p, p ∈ current ∧
          q ∈ A.transition p symbol from
          ⟨p, hp'.2, htransition⟩)
  · rintro ⟨hq, hstep⟩
    have hex : ∃ p, p ∈ current ∧
        q ∈ A.transition p symbol := by
      simpa [NFA.step] using hstep
    obtain ⟨p, hp, htransition⟩ := hex
    have hpstate := hcurrent p hp
    have hpsub := (hrel p).mpr ⟨hpstate, hp⟩
    exact ⟨hq, p, hpsub, htransition⟩

end FormalAutomata

namespace FormalAutomata

/-- The finite subset DFA's initial state represents
    exactly the original NFA's initial states. -/
theorem finite_subset_initial_membership
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (q : Q) :
    q ∈ (finiteSubsetDFA A).initial ↔
      q ∈ A.initial := by
  change q ∈ canonicalSubset A.states A.initial ↔
    q ∈ A.initial
  rw [mem_canonicalSubset]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨initial_states_valid A hA q h, h⟩

end FormalAutomata

namespace FormalAutomata

/-- If a canonical subset represents the current NFA states,
    one finite subset-DFA transition represents the next
    NFA state set, restricted to declared states. -/
theorem finite_subset_next_relation
    [DecidableEq Q]
    (A : NFA Q α)
    (currentSubset current : List Q)
    (hrel : ∀ p,
      p ∈ currentSubset ↔
        p ∈ A.states ∧ p ∈ current)
    (hcurrent : ∀ p, p ∈ current → p ∈ A.states)
    (symbol : α) :
    ∀ q,
      q ∈ (finiteSubsetDFA A).transition currentSubset symbol
        ↔
      q ∈ A.states ∧ q ∈ NFA.step A current symbol := by
  intro q
  exact finite_subset_transition_membership
    A currentSubset current hrel hcurrent symbol q

end FormalAutomata

namespace FormalAutomata

/-- After processing any valid input word, the finite subset
    DFA represents exactly the declared states reached by
    the original NFA. -/
theorem finite_subset_run_relation
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (currentSubset current : List Q)
    (hrel : ∀ q,
      q ∈ currentSubset ↔
        q ∈ A.states ∧ q ∈ current)
    (hcurrent : ∀ q, q ∈ current → q ∈ A.states)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    ∀ q,
      q ∈ word.foldl
        (fun states symbol =>
          (finiteSubsetDFA A).transition states symbol)
        currentSubset
      ↔
      q ∈ A.states ∧
        q ∈ word.foldl
          (fun states symbol =>
            NFA.step A states symbol)
          current := by
  induction word generalizing currentSubset current with
  | nil =>
      intro q
      simp only [List.foldl_nil]
      exact hrel q
  | cons a word ih =>
      simp only [List.foldl_cons]
      apply ih
      · intro q
        exact finite_subset_next_relation
          A currentSubset current hrel hcurrent a q
      · intro q hq
        exact step_states_valid A hA current hcurrent a
          (hword a (by simp)) q hq
      · intro b hb
        exact hword b (by simp [hb])

end FormalAutomata

namespace FormalAutomata

/-- The finite subset DFA and original NFA reach the same
    declared states after processing any valid input word. -/
theorem finite_subset_initial_run_relation
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    ∀ q,
      q ∈ DFA.run (finiteSubsetDFA A) word ↔
      q ∈ A.states ∧ q ∈ NFA.run A word := by
  have hrel :
      ∀ q,
        q ∈ (finiteSubsetDFA A).initial ↔
        q ∈ A.states ∧ q ∈ A.initial.eraseDups := by
    intro q
    change q ∈ canonicalSubset A.states A.initial ↔ _
    rw [mem_canonicalSubset]
    constructor
    · rintro ⟨hs, hi⟩
      exact ⟨hs, by simpa using hi⟩
    · rintro ⟨hs, hi⟩
      exact ⟨hs, by simpa using hi⟩

  have hcurrent :
      ∀ q, q ∈ A.initial.eraseDups → q ∈ A.states := by
    intro q hq
    exact initial_states_valid A hA q (by simpa using hq)

  unfold DFA.run NFA.run
  exact finite_subset_run_relation
    A hA
    (finiteSubsetDFA A).initial
    A.initial.eraseDups
    hrel hcurrent word hword

end FormalAutomata

namespace FormalAutomata

/-- The finite subset DFA accepts exactly the words
    accepted by the original well-formed NFA,
    provided the input belongs to the NFA alphabet. -/
theorem finite_subset_acceptance_preserved
    [DecidableEq Q]
    (A : NFA Q α)
    (hA : WellFormed A)
    (word : List α)
    (hword : ∀ a, a ∈ word → a ∈ A.alphabet) :
    DFA.accepts (finiteSubsetDFA A) word =
      NFA.accepts A word := by
  have hrun :=
    finite_subset_initial_run_relation A hA word hword

  change
    (DFA.run (finiteSubsetDFA A) word).any
      (fun q => A.accepting.contains q) =
    (NFA.run A word).any
      (fun q => A.accepting.contains q)

  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hd
    obtain ⟨q, hq, ha⟩ := List.any_eq_true.mp hd
    apply List.any_eq_true.mpr
    exact ⟨q, (hrun q).mp hq |>.2, ha⟩
  · intro hn
    obtain ⟨q, hq, ha⟩ := List.any_eq_true.mp hn
    have haccept : q ∈ A.accepting := by
      simpa using ha
    have hstate : q ∈ A.states :=
      accepting_states_valid A hA q haccept
    apply List.any_eq_true.mpr
    exact ⟨q, (hrun q).mpr ⟨hstate, hq⟩, ha⟩

end FormalAutomata
