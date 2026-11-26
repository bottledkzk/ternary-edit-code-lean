import EditCodes.Basic

namespace EditCodes
namespace Ternary

abbrev Word := List (Fin 3)

/-- Breadth-first numbering of ternary words. Removing the head takes a vertex to its parent. -/
def number : Word → Nat
  | [] => 0
  | a :: w => 3 * number w + a.val + 1

def word : Nat → Word
  | 0 => []
  | i + 1 => ⟨i % 3, by omega⟩ :: word (i / 3)
termination_by i => i

@[simp] theorem word_number (w : Word) : word (number w) = w := by
  induction w with
  | nil => simp [number, word]
  | cons a w ih =>
    rw [number, word]
    have hm : (3 * number w + a.val) % 3 = a.val := by omega
    have hd : (3 * number w + a.val) / 3 = number w := by omega
    simp [hm, hd, ih]

def wordCount : Nat → Nat
  | 0 => 1
  | n + 1 => 3 * wordCount n + 1

theorem number_lt {n : Nat} {w : Word} (h : w.length ≤ n) : number w < wordCount n := by
  induction n generalizing w with
  | zero => obtain rfl : w = [] := List.length_eq_zero_iff.mp (by omega); decide
  | succ n ih =>
    cases w with
    | nil => simp [number, wordCount]
    | cons a w =>
      have ht := ih (w := w) (by simpa using h)
      simp only [number, wordCount]
      omega

/-- Tabulation in increasing order. The step can inspect every earlier result. -/
private def tabulate (count : Nat) (step : Nat → Array β → β) : Array β :=
  (List.range count).foldl (fun acc i => acc.push (step i acc)) #[]

private theorem tabulate_succ (n : Nat) (step : Nat → Array β → β) :
    tabulate (n+1) step = (tabulate n step).push (step n (tabulate n step)) := by
  simp [tabulate, List.range_succ, List.foldl_append]

private theorem tabulate_size (n : Nat) (step : Nat → Array β → β) :
    (tabulate n step).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tabulate_succ, ih]

private theorem tabulate_correct [Inhabited β] (P : Nat → β → Prop) (step : Nat → Array β → β)
    (bound : Nat) (hs : ∀ i < bound, ∀ a, (∀ j < i, P j (a[j]?.getD default)) → P i (step i a))
    (n : Nat) (hn : n ≤ bound) (i : Nat) (hi : i < n) : P i ((tabulate n step)[i]?.getD default) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [tabulate_succ]
    by_cases he : i = n
    · subst i
      rw [Array.getElem?_push, tabulate_size, if_pos rfl]
      exact hs n (by omega) (tabulate n step) (ih (by omega))
    · have hl : i < (tabulate n step).size := by rw [tabulate_size]; omega
      simpa [Array.getElem?_push, hl, tabulate_size, he] using ih (by omega) i (by omega)

private def entry (row : Array Nat) (i : Nat) := row[i]?.getD 0

private def rowStep (size i : Nat) (rows : Array (Array Nat)) : Array Nat :=
  match i with
  | 0 => (List.range size).toArray.map (fun j => (word j).length)
  | p + 1 =>
    let old := rows[p / 3]?.getD #[]
    tabulate size fun j cur =>
      match j with
      | 0 => (word (p / 3)).length + 1
      | t + 1 =>
        min (entry old (t / 3) + (if p % 3 = t % 3 then 0 else 1))
          (1 + min (entry old (t + 1)) (entry cur (t / 3)))

private def table (size : Nat) := tabulate size (rowStep size)

private theorem row_correct {size i j : Nat} (hi : i < size) (hj : j < size) :
    entry ((table size)[i]?.getD #[]) j = distance (word i) (word j) := by
  let P (x : Nat) (r : Array Nat) := ∀ y < size, entry r y = distance (word x) (word y)
  suffices h : P i ((table size)[i]?.getD #[]) from h j hj
  apply tabulate_correct P (rowStep size) size _ size (Nat.le_refl _) i hi
  intro x hx a ha y hy
  cases x with
  | zero => simp [rowStep, entry, word, hy]
  | succ p =>
    have old := ha (p / 3) (by omega)
    change ∀ z < size, entry (a[p / 3]?.getD #[]) z = distance (word (p / 3)) (word z) at old
    unfold rowStep entry
    apply tabulate_correct (fun z val => val = distance (word (p+1)) (word z))
      _ size _ size (Nat.le_refl _) y hy
    intro t ht cur hcur
    cases t with
    | zero => simp [word]
    | succ t =>
      simp only [word, distance_cons, Fin.mk.injEq]
      unfold entry at old
      have hc : cur[t/3]?.getD 0 = distance (word (p+1)) (word (t/3)) := hcur _ (by omega)
      rw [old (t/3) (by omega), old (t+1) ht, hc]
      simp only [word]

private def pack (flags : List Bool) : Nat :=
  flags.foldr (fun b tail => (tail <<< 1) ||| b.toNat) 0

private theorem pack_bit (bs : List Bool) (i : Nat) :
    (pack bs).testBit i = bs[i]?.getD false := by
  induction bs generalizing i with
  | nil => simp [pack]
  | cons b bs ih =>
    change (((pack bs) <<< 1) ||| b.toNat).testBit i = _
    cases i with
    | zero => cases b <;> simp [Nat.testBit_shiftLeft]
    | succ i =>
      have hone : Nat.testBit 1 (i+1) = false := by rw [Nat.testBit_add_one]; simp
      cases b <;> simp [Nat.testBit_shiftLeft, hone, ih]

abbrev universeSize := wordCount 8

/-- Row i has bit j set when the decoded words have distance at least d. -/
@[noinline] def graphAt (size d : Nat) : Array Nat :=
  (table size).map fun row => pack (row.toList.map (fun v => decide (d ≤ v)))

theorem graphAt_bit {size d i j : Nat} (hd : 0 < d) (hi : i < size) (hj : j < size) :
    ((graphAt size d)[i]?.getD 0).testBit j = decide (d ≤ distance (word i) (word j)) := by
  have hsize : (table size).size = size := tabulate_size ..
  have hr := row_correct hi hj
  have hrow (r : Array Nat) :
      (pack (r.toList.map (fun v => decide (d ≤ v)))).testBit j = decide (d ≤ entry r j) := by
    rw [pack_bit]
    simp only [List.getElem?_map, Array.getElem?_toList, entry]
    have bit (o : Option Nat) :
        (o.map (fun v => decide (d ≤ v))).getD false = decide (d ≤ o.getD 0) := by
      cases o <;> simp [Nat.not_le.mpr hd]
    exact bit _
  simp only [graphAt, Array.getElem?_map]
  cases he : (table size)[i]? with
  | none => simp [Array.getElem?_eq_none_iff, hsize, Nat.not_le_of_lt hi] at he
  | some r => simpa [he, hrow] using congrArg (fun v => decide (d ≤ v)) hr

abbrev graphFor (size : Nat) := graphAt size 6

theorem graph_bit {i j : Nat} (hi : i < universeSize) (hj : j < universeSize) :
    ((graphFor universeSize)[i]?.getD 0).testBit j = decide (6 ≤ distance (word i) (word j)) :=
  graphAt_bit (by decide) hi hj

/-- The bitmask of long words whose initial letter has the requested value. -/
private def makeColourMask (c : Nat) : Nat :=
  pack ((List.range universeSize).map (fun i => decide (6 ≤ (word i).length ∧ (i-1)%3 = c)))

def colourMask : Nat → Nat
  | 0 => makeColourMask 0
  | 1 => makeColourMask 1
  | 2 => makeColourMask 2
  | _ + 3 => 0

theorem colourMask_bit {i c : Nat} (hi : i < universeSize) :
    (colourMask c).testBit i = decide (6 ≤ (word i).length ∧ (i-1)%3 = c) := by
  have hm (b : Nat) : (makeColourMask b).testBit i =
      decide (6 ≤ (word i).length ∧ (i-1)%3 = b) := by simp [makeColourMask, pack_bit, hi]
  match c with
  | 0 | 1 | 2 => exact hm _
  | b+3 =>
    have h : (i-1)%3 ≠ b+3 := by omega
    simp [colourMask, h]

def longMask : Nat :=
  pack ((List.range universeSize).map (fun i => decide (6 ≤ (word i).length)))

theorem longMask_bit {i : Nat} (hi : i < universeSize) (h : 6 ≤ (word i).length) :
    longMask.testBit i = true := by
  simp [longMask, pack_bit, hi, h]

end Ternary
end EditCodes
