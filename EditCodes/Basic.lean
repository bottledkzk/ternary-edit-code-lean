import Std

namespace EditCodes

variable {α : Type} [DecidableEq α]

/-- One row of the unit-cost Wagner–Fischer recurrence, expressed on suffixes. -/
private def extend (a : α) (prev : List α → Nat) (base : Nat) : List α → Nat
  | [] => base
  | b :: bs => min (prev bs + (if a = b then 0 else 1))
      (1 + min (prev (b :: bs)) (extend a prev base bs))

/-- Levenshtein distance with insertion, deletion and substitution each costing one. -/
def distance : List α → List α → Nat
  | [] => List.length
  | a :: as => extend a (distance as) (as.length + 1)

@[simp] theorem distance_nil_left (v : List α) : distance [] v = v.length := rfl

@[simp] theorem distance_nil_right (u : List α) : distance u [] = u.length := by
  cases u <;> rfl

theorem distance_cons (a b : α) (u v : List α) :
    distance (a :: u) (b :: v) =
      min (distance u v + (if a = b then 0 else 1))
        (1 + min (distance u (b :: v)) (distance (a :: u) v)) := rfl

/-- Equal symbols in corresponding positions up to the end of the shorter word. -/
def agreements : List α → List α → Nat
  | a :: u, b :: v => (if a = b then 1 else 0) + agreements u v
  | _, _ => 0

/-- Align the common-length prefixes, then insert or delete the leftover suffix. -/
theorem distance_add_matches_le (u v : List α) :
    distance u v + agreements u v ≤ max u.length v.length := by
  induction u generalizing v with
  | nil => simp [agreements]
  | cons a u ih =>
    cases v with
    | nil => simp [agreements]
    | cons b v =>
      have h := ih v
      rw [distance_cons, agreements]
      simp only [List.length_cons]
      split <;> omega

theorem distance_le_max_length (u v : List α) :
    distance u v ≤ max u.length v.length := by
  have := distance_add_matches_le u v
  omega

/-- A finite code is presented by its list of distinct words. -/
structure IsCode (n d : Nat) (C : List (List α)) : Prop where
  nodup : C.Nodup
  bounded : ∀ w ∈ C, w.length ≤ n
  separated : C.Pairwise (fun u v => d ≤ distance u v)

/-- The witness reaches length n; the upper bound covers every code of lengths at most n. -/
def OptimalSize (α : Type) [DecidableEq α] (n d m : Nat) : Prop :=
  (∃ C : List (List α), IsCode n d C ∧ C.length = m ∧ ∃ w ∈ C, w.length = n) ∧
  ∀ C : List (List α), IsCode n d C → C.length ≤ m

def longWords (d : Nat) (C : List (List α)) : List (List α) :=
  C.filter (fun w => decide (d ≤ w.length))

omit [DecidableEq α] in
theorem mem_longWords {d : Nat} {C : List (List α)} {w : List α} :
    w ∈ longWords d C ↔ w ∈ C ∧ d ≤ w.length := by simp [longWords]

/-- Two words shorter than d can be edited into one another in fewer than d steps. -/
theorem length_le_long_add_one {d : Nat} {C : List (List α)}
    (h : C.Pairwise (fun u v => d ≤ distance u v)) :
    C.length ≤ (longWords d C).length + 1 := by
  induction C with
  | nil => simp [longWords]
  | cons w ws ih =>
    obtain ⟨hw, ht⟩ := List.pairwise_cons.mp h
    by_cases hlen : d ≤ w.length
    · simpa [longWords, hlen] using Nat.succ_le_succ (ih ht)
    · have hall : ∀ v ∈ ws, d ≤ v.length := by
        intro v hv
        have := hw v hv
        have := distance_le_max_length w v
        omega
      have heq : longWords d ws = ws := by
        apply List.filter_eq_self.mpr
        simpa using hall
      simpa [longWords, hlen] using Nat.le_of_eq (congrArg List.length heq.symm)

end EditCodes
