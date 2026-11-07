import Std

namespace FormalAutomata.Epsilon

/-- An NFA with a separate epsilon-transition function. -/
structure ENFA (Q α : Type) where
  states : List Q
  alphabet : List α
  initial : List Q
  accepting : List Q
  epsilon : Q → List Q
  transition : Q → α → List Q

variable {Q α : Type} [DecidableEq Q]

/-- One epsilon-transition from a set of states. -/
def epsilonStep (A : ENFA Q α) (current : List Q) : List Q :=
  (current.flatMap A.epsilon).eraseDups

/--
Compute epsilon closure by repeatedly following epsilon edges.
The fuel is the number of declared states.
-/
def epsilonClosureFuel (A : ENFA Q α) : Nat → List Q → List Q
  | 0, current => current
  | n + 1, current =>
      epsilonClosureFuel A n ((current ++ epsilonStep A current).eraseDups)

/-- Epsilon closure of a set of states. -/
def epsilonClosure (A : ENFA Q α) (current : List Q) : List Q :=
  epsilonClosureFuel A A.states.length current

/-- Consume one input symbol, then follow all epsilon transitions. -/
def step (A : ENFA Q α) (current : List Q) (symbol : α) : List Q :=
  epsilonClosure A
    ((epsilonClosure A current).flatMap
      (fun q => A.transition q symbol))

/-- Execute a word, including epsilon closure before the first symbol. -/
def run (A : ENFA Q α) (word : List α) : List Q :=
  word.foldl (fun current symbol => step A current symbol)
    (epsilonClosure A A.initial)

/-- Accept if some reachable state is accepting. -/
def accepts (A : ENFA Q α) (word : List α) : Bool :=
  (run A word).any fun q => A.accepting.contains q

/-- A path may traverse epsilon edges without consuming input. -/
inductive Path (A : ENFA Q α) : Q → List α → Q → Prop
  | nil (q : Q) : Path A q [] q
  | epsilon {q q' r : Q} {word : List α}
      (hedge : q' ∈ A.epsilon q)
      (htail : Path A q' word r) :
      Path A q word r
  | symbol {q q' r : Q} {a : α} {word : List α}
      (hedge : q' ∈ A.transition q a)
      (htail : Path A q' word r) :
      Path A q (a :: word) r

/-- Acceptance defined independently through an accepting path. -/
def acceptsPath (A : ENFA Q α) (word : List α) : Prop :=
  ∃ q₀ qf, q₀ ∈ A.initial ∧
    qf ∈ A.accepting ∧ Path A q₀ word qf

/-- Every initial state must be declared. -/
def WellFormed (A : ENFA Q α) : Prop :=
  (∀ q, q ∈ A.initial → q ∈ A.states) ∧
  (∀ q, q ∈ A.accepting → q ∈ A.states) ∧
  (∀ q q', q ∈ A.states → q' ∈ A.epsilon q → q' ∈ A.states) ∧
  (∀ q a q', q ∈ A.states → a ∈ A.alphabet →
    q' ∈ A.transition q a → q' ∈ A.states)

def exampleENFA : ENFA Nat Bool where
  states := [0, 1, 2, 3, 4]
  alphabet := [true]
  initial := [0]
  accepting := [4]
  epsilon := fun q =>
    if q = 0 then [1]
    else if q = 1 then [0, 2]
    else if q = 3 then [4]
    else []
  transition := fun q a =>
    if q = 2 && a then [3] else []

example : accepts exampleENFA [true] = true := by decide

example : accepts exampleENFA [] = false := by decide

example : epsilonClosure exampleENFA [0] = [0, 1, 2] := by decide
example : acceptsPath exampleENFA [true] := by
  refine ⟨0, 4, ?_, ?_, ?_⟩
  · simp [exampleENFA]
  · simp [exampleENFA]
  · exact Path.epsilon (A := exampleENFA) (q := 0) (q' := 1)
      (r := 4) (word := [true]) (by simp [exampleENFA])
      (Path.epsilon (A := exampleENFA) (q := 1) (q' := 2)
        (r := 4) (word := [true]) (by simp [exampleENFA])
        (Path.symbol (A := exampleENFA) (q := 2) (q' := 3)
          (r := 4) (a := true) (word := [])
          (by simp [exampleENFA])
          (Path.epsilon (A := exampleENFA) (q := 3) (q' := 4)
            (r := 4) (word := []) (by simp [exampleENFA])
            (Path.nil 4))))

example : WellFormed exampleENFA := by
  unfold WellFormed
  constructor
  · intro q h
    simp_all [exampleENFA]
  · constructor
    · intro q h
      simp_all [exampleENFA]
    · constructor
      · intro q q' hq hedge
        simp [exampleENFA] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · simp [exampleENFA] at hedge
          subst q'
          simp [exampleENFA]
        · simp [exampleENFA] at hedge
          rcases hedge with h | h
          · subst q'
            simp [exampleENFA]
          · subst q'
            simp [exampleENFA]
        · simp [exampleENFA] at hedge
        · simp [exampleENFA] at hedge
          subst q'
          simp [exampleENFA]
        · simp [exampleENFA] at hedge
      · intro q a q' hq ha hedge
        simp [exampleENFA] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · simp [exampleENFA] at hedge
        · simp [exampleENFA] at hedge
        · simp [exampleENFA] at hedge
          rcases hedge with ⟨ha', hq'⟩
          subst a
          subst q'
          simp [exampleENFA]
        · simp [exampleENFA] at hedge
        · simp [exampleENFA] at hedge
end FormalAutomata.Epsilon

