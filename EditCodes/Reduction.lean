import EditCodes.Decision

namespace EditCodes

theorem distance_comm {α : Type} [DecidableEq α] (u v : List α) :
    distance u v = distance v u := by
  cases u with
  | nil => simp
  | cons a us =>
    cases v with
    | nil => simp
    | cons b vs =>
      rw [distance_cons a b, distance_cons b a, distance_comm us vs,
        distance_comm us (b :: vs), distance_comm (a :: us) vs]
      by_cases e : a = b <;> simp [e, Ne.symm, Nat.min_comm]
termination_by u.length + v.length

private theorem rel_of_distinct_mem {R : α → α → Prop} (sym : ∀ x y, R x y → R y x)
    {xs : List α} (h : xs.Pairwise R) {x y : α} (hx : x ∈ xs) (hy : y ∈ xs)
    (hne : x ≠ y) : R x y := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hx with hx0 | hxTail
    · rcases List.mem_cons.mp hy with hy0 | hyTail
      · exact False.elim (hne (hx0.trans hy0.symm))
      · exact hx0 ▸ ha _ hyTail
    · rcases List.mem_cons.mp hy with hy0 | hyTail
      · exact hy0 ▸ sym _ _ (ha _ hxTail)
      · exact ih ht hxTail hyTail

namespace Ternary
open Search

local notation "G₈" => adjacency (graphFor universeSize)

private def colour (x : Nat) := (x-1)%3
private def classOf (xs : List Nat) (c : Nat) := xs.filter (fun x => decide (colour x = c))

private theorem class_count (xs : List Nat) :
    (classOf xs 0).length + (classOf xs 1).length + (classOf xs 2).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : colour x = 0 ∨ colour x = 1 ∨ colour x = 2 := by unfold colour; omega
    rcases h with h | h | h <;> simp [classOf, h] at ih ⊢ <;> omega

private theorem triple_phase (xs : List Nat) (c pickPool allPool : Nat) (finish : Nat → Bool)
    (nd : xs.Nodup) (good : Complete G₈ xs) (hthree : 3 ≤ (classOf xs c).length)
    (hclass : ∀ u ∈ xs, colour u = c → pickPool.testBit u = true) (hin : Inside xs allPool)
    (done : ∀ rest : List Nat, rest.length + 3 = xs.length → rest.Nodup → rest ⊆ xs →
      ∀ pool, Inside rest pool → finish pool = true) :
    choose G₈ finish 3 pickPool allPool = true := by
  let triple := (classOf xs c).take 3
  have hlen₃ : triple.length = 3 := List.length_take_of_le hthree
  have hsub : triple.Sublist xs := (List.take_sublist _ _).trans List.filter_sublist
  obtain ⟨rest, hp⟩ := hsub.exists_perm_append
  have hlenRest : rest.length + 3 = xs.length := by
    have hh := hp.length_eq; rw [List.length_append, hlen₃] at hh; omega
  have nd' := hp.nodup_iff.mp nd
  have hdisjoint := (List.pairwise_append.mp nd').2.2
  have hrsub {x : Nat} (h : x ∈ rest) : x ∈ xs :=
    hp.mem_iff.mpr (List.mem_append_right _ h)
  rw [← hlen₃]
  apply choose_complete G₈ _ triple rest _ _ (nd.sublist hsub)
  · exact fun u hu v hv => good _ (hsub.subset hu) _ (hsub.subset hv)
  · exact fun u hu v hv => good _ (hsub.subset hu) _ (hrsub hv) (hdisjoint _ hu _ hv)
  · intro u hu
    have hc : u ∈ classOf xs c := (List.take_sublist _ _).subset hu
    exact hclass u (hsub.subset hu) (of_decide_eq_true (List.mem_filter.mp hc).2)
  · intro u hu
    exact hin _ (hrsub hu)
  · exact done rest hlenRest (List.pairwise_append.mp nd').2.1 (fun _ h => hrsub h)

private theorem nonzero_of_bit {s i : Nat} (h : s.testBit i = true) : s ≠ 0 := by
  intro hz; simp [hz] at h

private theorem edge_of_pair (xs : List Nat) (hlen : xs.length = 2) (nd : xs.Nodup)
    (good : Complete G₈ xs) (pool : Nat) (hin : Inside xs pool) : hasEdge G₈ pool = true := by
  match xs with
  | [] | [_] => simp at hlen
  | a :: b :: t =>
    have ha : a ∈ a :: b :: t := by simp
    have hb : b ∈ a :: b :: t := by simp
    have ne : a ≠ b := fun e => (List.nodup_cons.mp nd).1 (by simp [e])
    apply List.any_eq_true.mpr
    refine ⟨a, mem_members (hin _ ha), bne_iff_ne.mpr (nonzero_of_bit (i := b) ?_)⟩
    simp [hin b hb, good a ha b hb ne]

private theorem five_of_clique (xs : List Nat) (hlen : xs.length = 5) (nd : xs.Nodup)
    (good : Complete G₈ xs) (bounds : ∀ x ∈ xs, x < universeSize ∧ 6 ≤ (word x).length)
    (c : Nat) (hc : c ∈ [0,1,2]) (pool : Nat) (hin : Inside xs pool) :
    possibleFive G₈ c pool = true := by
  apply Bool.or_eq_true_iff.mpr
  by_cases hzero : pool &&& colourMask c = 0
  · apply Or.inr
    have hempty : classOf xs c = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro u hu
      obtain ⟨hm, he⟩ := List.mem_filter.mp hu
      obtain ⟨hi, hl⟩ := bounds u hm
      have heq : colour u = c := of_decide_eq_true he
      have hcol := (colourMask_bit (c := c) hi).trans (decide_eq_true ⟨hl, heq⟩)
      exact nonzero_of_bit (s := pool &&& colourMask c) (i := u) (by simp [hin u hm, hcol]) hzero
    have h0 : (classOf xs c).length = 0 := by rw [hempty]; rfl
    have hex : ∃ b ∈ [0,1,2], 3 ≤ (classOf xs b).length := by
      have hs := class_count xs
      by_cases h : 3 ≤ (classOf xs 0).length
      · exact ⟨0, by decide, h⟩
      by_cases h' : 3 ≤ (classOf xs 1).length
      · exact ⟨1, by decide, h'⟩
      refine ⟨2, by decide, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> omega
    obtain ⟨b, hb, h3⟩ := hex
    have hne : b ≠ c := by intro e; subst b; omega
    apply List.any_eq_true.mpr
    refine ⟨b,hb, Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr hne, ?_⟩⟩
    refine triple_phase xs b _ _ _ nd good h3 ?_ hin ?_
    · intro u hu he
      obtain ⟨hi, hl⟩ := bounds u hu
      simp only [Nat.testBit_and, hin u hu, Bool.true_and, colourMask_bit hi]
      exact decide_eq_true ⟨hl, he⟩
    · intro rest hr ndRest sub next inside
      exact edge_of_pair rest (by omega) ndRest (fun u hu v hv => good u (sub hu) v (sub hv)) next inside
  · exact Or.inl (bne_iff_ne.mpr hzero)

/-- Any eight long codewords imply that the finite search must accept. -/
theorem accepts_eight (xs : List Nat) (hlen : xs.length = 8) (nd : xs.Nodup)
    (good : Complete G₈ xs) (bounds : ∀ x ∈ xs, x < universeSize ∧ 6 ≤ (word x).length) :
    possibleEight universeSize = true := by
  have hc : ∃ c ∈ [0,1,2], 3 ≤ (classOf xs c).length := by
    have h := class_count xs
    by_cases h0 : 3 ≤ (classOf xs 0).length
    · exact ⟨0, by decide, h0⟩
    by_cases h1 : 3 ≤ (classOf xs 1).length
    · exact ⟨1, by decide, h1⟩
    exact ⟨2, by decide, by omega⟩
  obtain ⟨c, hc, h3⟩ := hc
  apply List.any_eq_true.mpr
  refine ⟨c, hc, ?_⟩
  apply triple_phase xs c _ _ _ nd good h3
  · intro u hu he
    obtain ⟨hi,hl⟩ := bounds u hu
    exact (colourMask_bit hi).trans (decide_eq_true ⟨hl, he⟩)
  · intro u hu
    obtain ⟨hi,hl⟩ := bounds u hu
    exact longMask_bit hi hl
  · intro rest hr ndRest sub next inside
    exact five_of_clique rest (by omega) ndRest (fun u hu v hv => good u (sub hu) v (sub hv))
      (fun u hu => bounds u (sub hu)) c hc next inside

/-- Every nine-word code would supply at least eight long words to the search. -/
theorem upper_of_search (hempty : possibleEight universeSize = false) (C : List Word) (h : IsCode 8 6 C) :
    C.length ≤ 8 := by
  have hcount := length_le_long_add_one h.separated
  by_cases hlen : 8 ≤ (longWords 6 C).length
  · let chosen := (longWords 6 C).take 8
    have hlen₈ : chosen.length = 8 := List.length_take_of_le hlen
    have hsub : chosen.Sublist C := (List.take_sublist _ _).trans List.filter_sublist
    have hlong {w : Word} (hw : w ∈ chosen) : 6 ≤ w.length :=
      (mem_longWords.mp ((List.take_sublist _ _).subset hw)).2
    let xs := chosen.map number
    have nd : xs.Nodup := by
      apply List.pairwise_map.mpr
      apply (h.nodup.sublist hsub).imp
      intro a b hab he
      exact hab (by simpa using congrArg word he)
    have bounds (i) (hi : i ∈ xs) : i < universeSize ∧ 6 ≤ (word i).length := by
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hi
      exact ⟨number_lt (h.bounded u (hsub.subset hu)), by simpa using hlong hu⟩
    have good : Complete G₈ xs := by
      intro i hi j hj hne
      change ((graphFor universeSize)[i]?.getD 0).testBit j = true
      rw [graph_bit (bounds _ hi).1 (bounds _ hj).1]
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hj
      simp only [word_number, decide_eq_true_eq]
      apply rel_of_distinct_mem (R := fun a b => 6 ≤ distance a b)
        (fun a b hh => Nat.le_trans hh (Nat.le_of_eq (distance_comm a b)))
        h.separated (hsub.subset hu) (hsub.subset hv)
      exact fun e => hne (congrArg number e)
    have hyes := accepts_eight xs (by simpa [xs] using hlen₈) nd good bounds
    simp [hempty] at hyes
  · omega

end Ternary
end EditCodes
