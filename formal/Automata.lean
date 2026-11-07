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
