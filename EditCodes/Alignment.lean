import EditCodes.Basic

namespace EditCodes

variable {α : Type} [DecidableEq α]

/-- A left-to-right alignment with a stated number of unit edits.
Matching equal symbols is free. A gap accounts for one insertion or deletion. -/
inductive Alignment : List α → List α → Nat → Prop where
  | empty : Alignment [] [] 0
  | delete (a : α) : Alignment u v k → Alignment (a :: u) v (k + 1)
  | insert (b : α) : Alignment u v k → Alignment u (b :: v) (k + 1)
  | pair (a b : α) : Alignment u v k → Alignment (a :: u) (b :: v) (k + if a = b then 0 else 1)

theorem Alignment.distance_le {u v : List α} {k} (h : Alignment u v k) :
    distance u v ≤ k := by
  induction h with
  | empty => simp
  | @delete u v k a _ ih =>
    cases v with
    | nil => simpa using Nat.succ_le_succ ih
    | cons b bs => rw [distance_cons]; omega
  | @insert u v k b _ ih =>
    cases u with
    | nil => simpa using Nat.succ_le_succ ih
    | cons a as => rw [distance_cons]; omega
  | pair a b _ ih => rw [distance_cons]; omega

theorem distance_attained (u v : List α) : Alignment u v (distance u v) := by
  cases u with
  | nil =>
    cases v with
    | nil => exact .empty
    | cons b v => exact .insert b (distance_attained [] v)
  | cons a u =>
    cases v with
    | nil => simpa using Alignment.delete a (distance_attained u [])
    | cons b v =>
      rw [distance_cons]
      by_cases hd : distance u v + (if a = b then 0 else 1) ≤
          1 + min (distance u (b :: v)) (distance (a :: u) v)
      · rw [Nat.min_eq_left hd]
        exact .pair a b (distance_attained u v)
      · rw [Nat.min_eq_right (by omega)]
        by_cases hi : distance u (b :: v) ≤ distance (a :: u) v
        · rw [Nat.min_eq_left hi, Nat.add_comm]
          exact .delete a (distance_attained u (b :: v))
        · rw [Nat.min_eq_right (by omega), Nat.add_comm]
          exact .insert b (distance_attained (a :: u) v)
termination_by u.length + v.length

end EditCodes
