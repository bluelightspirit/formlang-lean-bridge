import Std

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
