import Std

namespace EditCodes.Search

/-- Retain the bits at indices strictly below i. -/
def below (s i : Nat) := s &&& ((1 <<< i) - 1)

theorem below_bit (s i j : Nat) :
    (below s i).testBit j = (s.testBit j && decide (j < i)) := by
  simp [below, Nat.shiftLeft_eq, Bool.and_comm]

private theorem below_top_lt (s : Nat) (h : s ≠ 0) : below s s.log2 < s := by
  have h₁ : below s s.log2 ≤ (1 <<< s.log2) - 1 := Nat.and_le_right
  have h₂ := Nat.log2_self_le h
  simp [Nat.shiftLeft_eq] at h₁
  have := Nat.two_pow_pos s.log2
  omega

/-- Enumerate only set bits, from the largest index downwards. -/
def members (s : Nat) : List Nat :=
  if s = 0 then [] else s.log2 :: members (below s s.log2)
termination_by s
decreasing_by apply below_top_lt; assumption

theorem mem_members {s i : Nat} (h : s.testBit i = true) : i ∈ members s := by
  rw [members]
  split
  next hz => simp [hz] at h
  next hz =>
    by_cases e : i = s.log2
    · simp [e]
    · have hi : i ≤ s.log2 := (Nat.le_log2 hz).mpr (by
        by_cases hb : 2^i ≤ s
        · exact hb
        · have := Nat.testBit_lt_two_pow (x := s) (i := i) (by omega)
          simp_all)
      exact List.mem_cons_of_mem _ (mem_members (by simp [below_bit, h, show i < s.log2 by omega]))
termination_by s
decreasing_by apply below_top_lt; assumption

abbrev Neighbours := Nat → Nat

def Inside (xs : List Nat) (mask : Nat) := ∀ v ∈ xs, mask.testBit v = true

def Complete (G : Neighbours) (xs : List Nat) :=
  ∀ u ∈ xs, ∀ v ∈ xs, u ≠ v → (G u).testBit v = true

/-- Choose k pairwise adjacent vertices from pool in descending order. The continuation
receives the part of globalPool adjacent to every vertex chosen in this phase. -/
def choose (G : Neighbours) (finish : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, _, globalPool => finish globalPool
  | k + 1, pool, globalPool =>
    (members pool).any fun v =>
      let near := G v
      choose G finish k (below (pool &&& near) v) (globalPool &&& near)

/-- Every compatible choice is visited. The list ys is reserved for the continuation. -/
theorem choose_complete (G : Neighbours) (finish : Nat → Bool) (xs ys : List Nat)
    (pool globalPool : Nat) (nd : xs.Nodup) (complete : Complete G xs)
    (cross : ∀ u ∈ xs, ∀ v ∈ ys, (G u).testBit v = true)
    (hin : Inside xs pool) (hrest : Inside ys globalPool)
    (done : ∀ mask, Inside ys mask → finish mask = true) :
    choose G finish xs.length pool globalPool = true := by
  cases he : xs.max? with
  | none =>
    have hx : xs = [] := by
      cases xs with
      | nil => rfl
      | cons a as => simp [List.max?_cons] at he
    subst xs
    exact done _ hrest
  | some v =>
    obtain ⟨hv, hmax⟩ := List.max?_eq_some_iff'.mp he
    let rest := xs.erase v
    have hlen := List.length_erase_of_mem hv
    have hpos : 0 < xs.length := List.length_pos_of_mem hv
    have hsplit : xs.length = rest.length + 1 := by dsimp [rest]; omega
    rw [hsplit, choose, List.any_eq_true]
    refine ⟨v, mem_members (hin v hv), ?_⟩
    have hmem (u) (hu : u ∈ rest) := nd.mem_erase_iff.mp hu
    apply choose_complete G finish rest ys _ _ (nd.erase v)
    · exact fun u hu w hw => complete u (hmem u hu).2 w (hmem w hw).2
    · exact fun u hu => cross u (hmem u hu).2
    · intro u hu
      obtain ⟨hne, hx⟩ := hmem u hu
      have hlt : u < v := Nat.lt_of_le_of_ne (hmax u hx) hne
      simp [below_bit, hin u hx, complete v hv u hx (Ne.symm hne), hlt]
    · intro u hu
      simp [hrest u hu, cross v hv u hu]
    · exact done
termination_by xs.length
decreasing_by omega

end EditCodes.Search
