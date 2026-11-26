module
public import Symconf93.ActualSieveInput

@[expose] public section

/-! A sound weak-period exact local row decision. It uses degree, moments,
and aggregate period occupancy, but not an adjacent-zero or parity premise. -/
namespace Symconf93
open scoped BigOperators

def expenditure (a b u d : ℕ) : ℕ := if Nat.gcd a b∣d then u else 0

/-- Local witnesses normalized by the positive component length; the
remaining period budget is reduced branch by branch. -/
inductive RowWitness (a : ℕ) : List ℕ → ℕ → ℕ → (ℕ→ℕ) → Prop where
  | nil (cap : ℕ→ℕ) : RowWitness a [] 0 0 cap
  | cons (b : ℕ) (P : List ℕ) (u v s t : ℕ) (cap : ℕ→ℕ) :
      0<b → u≤10 → v≤10 → a*u=b*v →
      (∀ d,0<d → d<a → expenditure a b u d≤cap d) →
      RowWitness a P s t (fun d => cap d-expenditure a b u d) →
      RowWitness a (b::P) (u+s) (u*v+t) cap

def rowSieve93 (a : ℕ) (P : List ℕ) (s t : ℕ) (cap : ℕ→ℕ) : Bool :=
  match P with
  | [] => s==0 && t==0
  | b::Q => (List.range (min s 10+1)).any (fun u =>
      let v := (a*u)/b
      decide (0<b ∧ a*u=b*v ∧ v≤10 ∧ u*v≤t) &&
      ((List.range a).all (fun d => d==0 || decide (expenditure a b u d≤cap d))) &&
      rowSieve93 a Q (s-u) (t-u*v) (fun d=>cap d-expenditure a b u d))

theorem rowSieve93_complete {a : ℕ} {P : List ℕ} {s t : ℕ} {cap : ℕ→ℕ}
    (h : RowWitness a P s t cap) : rowSieve93 a P s t cap=true := by
  induction h with
  | nil cap => rfl
  | cons b P u v s t cap hb hu hv he hc htail ih =>
    have hV : a*u/b=v := by rw [he,Nat.mul_comm,Nat.mul_div_cancel _ hb]
    rw [rowSieve93,List.any_eq_true]
    refine ⟨u,?_,?_⟩
    · rw [List.mem_range,Nat.lt_succ_iff,Nat.le_min]
      exact ⟨Nat.le_add_right _ _,hu⟩
    · simp only [hV,Bool.and_eq_true,decide_eq_true_eq,Nat.add_sub_cancel_left]
      refine ⟨⟨⟨hb,he,hv,Nat.le_add_right _ _⟩,?_⟩,ih⟩
      apply List.all_eq_true.mpr
      intro d hd
      rw [List.mem_range] at hd
      by_cases h0 : d=0
      · simp [h0]
      · simp [hc d (by omega) hd]

/-- Actual column and row contributions give a literal decoder witness. -/
theorem rowWitness_of_weighted_moments (a : ℕ) (P : List ℕ)
    (u v : Fin P.length → ℕ) (cap : ℕ→ℕ)
    (hpos : ∀ b∈P,0<b) (hu : ∀ i,u i≤10) (hv : ∀ i,v i≤10)
    (he : ∀ i,a*u i=P.get i*v i)
    (hc : ∀ d,0<d → d<a →
      (∑ i, expenditure a (P.get i) (u i) d) ≤ cap d) :
    RowWitness a P (∑ i,u i) (∑ i,u i*v i) cap := by
  induction P generalizing cap with
  | nil =>
    simp only [List.length_nil,Finset.univ_eq_empty,Finset.sum_empty]
    exact RowWitness.nil cap
  | cons b Q ih =>
    change RowWitness a (b::Q) (∑ i : Fin (Q.length+1),u i)
      (∑ i : Fin (Q.length+1),u i*v i) cap
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
    refine RowWitness.cons b Q (u 0) (v 0) _ _ cap (hpos b (by simp))
      (hu 0) (hv 0) (he 0) ?_ ?_
    · intro d hd hda
      have h := hc d hd hda
      change (∑ i : Fin (Q.length+1),
        expenditure a ((b::Q).get i) (u i) d) ≤ cap d at h
      rw [Fin.sum_univ_succ] at h
      exact (Nat.le_add_right _ _).trans h
    · apply ih (fun i => u i.succ) (fun i => v i.succ)
      · exact fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      · exact fun i => hu i.succ
      · exact fun i => hv i.succ
      · exact fun i => he i.succ
      · intro d h0 ha
        have h := hc d h0 ha
        change (∑ i : Fin (Q.length+1),
          expenditure a ((b::Q).get i) (u i) d) ≤ cap d at h
        rw [Fin.sum_univ_succ] at h
        change expenditure a b (u 0) d+
          (∑ i : Fin Q.length, expenditure a (Q.get i) (u i.succ) d) ≤cap d at h
        omega

private theorem positive_profile_length {P : List ℕ} (F : OriginalProfileFacts P)
    (i : Fin P.length) : 0<P.get i :=
  lt_of_lt_of_le (by decide : 0<3) (F.positive _ (List.get_mem P i))

private theorem momentOne_normalize {P : List ℕ} (F : OriginalProfileFacts P)
    (i : Fin P.length) : (∑ j,(F.row i).u j)=10 := by
  have h := (F.row i).momentOne
  simp_rw [← (F.row i).block, ← Finset.mul_sum, Nat.mul_comm 10 (P.get i)] at h
  exact Nat.eq_of_mul_eq_mul_left (positive_profile_length F i) h

private theorem momentTwo_normalize {P : List ℕ} (F : OriginalProfileFacts P)
    (i : Fin P.length) : (∑ j,(F.row i).u j*(F.row i).v j)=P.get i+7 := by
  have h := (F.row i).momentTwo
  simp_rw [← (F.row i).block, mul_assoc, ← Finset.mul_sum] at h
  exact Nat.eq_of_mul_eq_mul_left (positive_profile_length F i) h

/-- Any ordered genuine profile passes every normalized row test. -/
theorem true_profile_passes_row_sieve {P : List ℕ} (F : OriginalProfileFacts P)
    (a : ℕ) (ha : a∈P) : rowSieve93 a P 10 (a+7) (fun _=>1)=true := by
  obtain ⟨i,hi⟩ := List.get_of_mem ha
  subst a
  have hhu (j : Fin P.length) : (F.row i).u j≤10 := by
    rw [← momentOne_normalize F i]
    exact Finset.single_le_sum (f:=(F.row i).u) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h := rowWitness_of_weighted_moments (P.get i) P (F.row i).u (F.row i).v
    (fun _=>1) (fun b hb => lt_of_lt_of_le (by decide : 0<3) (F.positive _ hb))
    hhu (F.cap i) (F.row i).block (F.period i)
  rw [momentOne_normalize F i,momentTwo_normalize F i] at h
  exact rowSieve93_complete h

/-- Length four is excluded purely by the positive gap from the
first-to-second weighted moment; no parity theorem is needed. -/
theorem no_length_four_moment {ι : Type*} [Fintype ι] {L : ι→ℕ}
    (hL : ∀ i,3≤L i) (R : ProfileRow L 4) : False := by
  have h1 : (∑ i,L i*R.v i)=40 := R.momentOne
  have h2 : (∑ i,L i*R.v i*R.v i)=44 := R.momentTwo
  have hn (i : ι) : L i*R.v i≤L i*R.v i*R.v i := by
    by_cases h : R.v i=0
    · simp [h]
    · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (L i*R.v i) (show 1≤R.v i by omega)
  have hs : (∑ i,(L i*R.v i*R.v i-L i*R.v i))=4 := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hn i),h1,h2]
  have hh (i : ι) : R.v i≤1 := by
    by_contra! hc
    have he := Finset.single_le_sum
      (f:=fun j => L j*R.v j*R.v j-L j*R.v j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hs] at he
    have hmul := Nat.mul_le_mul_left (L i*R.v i) hc
    have h6 : 6≤L i*R.v i := by
      have h6' := Nat.mul_le_mul (hL i) hc
      exact h6'
    omega
  have hzero : (∑ i, (L i*R.v i*R.v i-L i*R.v i))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have he : R.v i=0 ∨ R.v i=1 := by have := hh i; omega
    rcases he with he|he <;> simp [he]
  omega

def profileSieve93 (P : List ℕ) : Bool :=
  !(P.contains 4) && P.all (fun a => rowSieve93 a P 10 (a+7) (fun _=>1))

theorem true_profile_passes_sieve {P : List ℕ} (F : OriginalProfileFacts P) :
    profileSieve93 P=true := by
  unfold profileSieve93
  rw [Bool.and_eq_true]
  constructor
  · by_contra! h
    have h4 : 4∈P := by simpa using h
    obtain ⟨i,hi⟩ := List.get_of_mem h4
    have hR := F.row i
    rw [hi] at hR
    exact no_length_four_moment (fun j => F.positive _ (List.get_mem P j)) hR
  · exact List.all_eq_true.mpr (fun a ha => true_profile_passes_row_sieve F a ha)

end Symconf93

#print axioms Symconf93.rowSieve93_complete
#print axioms Symconf93.true_profile_passes_sieve
