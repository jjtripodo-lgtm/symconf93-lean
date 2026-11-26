module
public import Symconf93.LoosePrefix93

@[expose] public section

/-! A compact prefix overcount validated by actual remaining total, not
an optimistic external pruning hint. -/
namespace Symconf93
open scoped List

def possibleTailLength93 (a hi rem : Nat) : List Nat :=
  (List.range (min hi rem+1)).filter (fun b =>
    decide (3≤b ∧ b≠4) && relevant a b)

def inflatedTail93 (a hi rem : Nat) : List Nat :=
  (possibleTailLength93 a hi rem).flatMap (fun b => List.replicate (rem/b) b)

def inflatedPrefix93 (a hi rem : Nat) (P : List Nat) : List Nat :=
  P.filter (relevant a) ++ inflatedTail93 a hi rem

private theorem chunk_in_flatMap {A B : Type*} (f : A→List B) (L : List A)
    {b : A} (hb : b∈L) : f b <+ L.flatMap f := by
  induction L with
  | nil => simp at hb
  | cons a L ih =>
    rcases List.mem_cons.mp hb with rfl|hm
    · exact List.sublist_append_left _ _
    · exact (ih hm).trans (List.sublist_append_right _ _)

theorem actual_tail_filter_in_inflation (a hi rem : Nat) (T : List Nat)
    (hs : T.sum=rem) (h : ∀ b∈T, 3≤b ∧ b≠4 ∧ b≤hi) :
    T.filter (relevant a) <+~ inflatedTail93 a hi rem := by
  apply List.subperm_iff_count.mpr
  intro b
  by_cases hm : b∈T.filter (relevant a)
  · obtain ⟨hB,hRel⟩ := List.mem_filter.mp hm
    have ht := h b hB
    have hRem : b≤rem := hs ▸ Symconf59.member_le_sum hB
    have hBank : b∈possibleTailLength93 a hi rem := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_range.mpr (by omega),?_⟩
      simp [ht.1,ht.2.1,hRel]
    have hsub := chunk_in_flatMap (fun b => List.replicate (rem/b) b) _ hBank
    have hcb : (List.replicate (rem/b) b).count b ≤ (inflatedTail93 a hi rem).count b :=
      hsub.count_le b
    rw [List.count_replicate_self] at hcb
    have hC : T.count b≤rem/b := by
      have hp : 0<b := by omega
      have hcount := cycle_multiplicity_tail_bound b T
      exact (Nat.le_div_iff_mul_le hp).mpr (by simpa only [hs,Nat.mul_comm] using hcount)
    exact ((List.filter_sublist ..).count_le b).trans (hC.trans hcb)
  · rw [List.count_eq_zero_of_not_mem hm]
    exact Nat.zero_le _

private theorem inflated_all_positive (a hi rem : Nat) (P : List Nat)
    (hP : ∀ b∈P,3≤b) : ∀ b∈inflatedPrefix93 a hi rem P,0<b := by
  intro b hb
  rcases List.mem_append.mp hb with h1|h2
  · have hp := hP b (List.mem_filter.mp h1).1
    omega
  · obtain ⟨c,hc,hbc⟩ := List.mem_flatMap.mp h2
    have he : b=c := (List.mem_replicate.mp hbc).2
    subst c
    have hh := (List.mem_filter.mp hc).2
    simp at hh
    omega

theorem inflated_prefix_rejection_sound
    (P T : List Nat) (F : OriginalProfileFacts (P++T)) (a hi rem : Nat)
    (ha : a∈P) (hs : T.sum=rem) (hT : ∀ b∈T, 3≤b ∧ b≠4 ∧ b≤hi)
    (hfalse : rowLoose93 a (inflatedPrefix93 a hi rem P) 10 (a+7)=false) : False := by
  have hIn := actual_tail_filter_in_inflation a hi rem T hs hT
  have hInc : (P++T).filter (relevant a) <+~ inflatedPrefix93 a hi rem P := by
    rw [List.filter_append]
    apply List.subperm_iff_count.mpr
    intro b
    simp only [inflatedPrefix93,List.count_append]
    exact Nat.add_le_add_left (List.subperm_iff_count.mp hIn b) _
  exact dead_prefix_excludes_actual F (List.mem_append_left T ha) hInc
    (inflated_all_positive a hi rem P (fun b hb=>F.positive b (List.mem_append_left T hb))) hfalse

end Symconf93

#print axioms Symconf93.actual_tail_filter_in_inflation
#print axioms Symconf93.inflated_prefix_rejection_sound
