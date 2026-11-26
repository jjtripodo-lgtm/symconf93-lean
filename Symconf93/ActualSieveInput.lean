module
public import Symconf93.OriginalCoordinates
public import Symconf59.ProfileSieve

@[expose] public section

namespace Symconf93
open Matrix Symconf59
open scoped BigOperators

/-- The arithmetic input consists exclusively of both actual ordered
leave charts of the literal integer incidence matrix. -/
theorem actual_incidence_profile {A : Int93} (hA : Incidence93 A) :
    ∃ P : List ℕ, ∃ _R : OrderedCycles (rowLeave A) P,
      ∃ _C : OrderedCycles (colLeave A) P, Nonempty (OriginalProfileFacts P) := by
  obtain ⟨P,hs,hmin,hord,⟨R⟩,⟨C⟩⟩ := original_ordered_cycle_coords hA
  exact ⟨P,R,C,⟨physical_blocks_to_profile hA
    (physical_of_ordered_cycles hA hmin R C) hs hmin hord⟩⟩

/-- Exact parity-free enumeration domain.  Neither a small divisor
test nor cycle-count parity is assumed of the literal incidence. -/
theorem physical_profile_mem_parity_free {A : Int93} (hA : Incidence93 A) :
    ∃ P : List ℕ, P ∈ Symconf59.partitionLists 31 93 93 ∧
      ∃ _R : OrderedCycles (rowLeave A) P, ∃ _C : OrderedCycles (colLeave A) P,
        Nonempty (OriginalProfileFacts P) := by
  obtain ⟨P,R,C,⟨F⟩⟩ := actual_incidence_profile hA
  have hl (Q : List ℕ) (hQ : ∀ a∈Q,3≤a) : 3*Q.length≤Q.sum := by
    induction Q with
    | nil => decide
    | cons a L ih =>
      have ha := hQ a (by simp)
      have ht := ih (fun b hb => hQ b (List.mem_cons_of_mem _ hb))
      simp only [List.length_cons,List.sum_cons]
      omega
  have hlen := hl P F.positive
  have hn : P.length ≤ 31 := by rw [F.total] at hlen; omega
  have hb : ∀ b∈P,b≤93 := by
    intro b h
    simpa only [F.total] using Symconf59.member_le_sum h
  have he := Symconf59.partitionLists_complete P 31 93 hn F.positive hb F.ordered
  exact ⟨P,by simpa only [F.total] using he,R,C,⟨F⟩⟩

theorem no_three_seven_cross_moment {ι : Type*} [Fintype ι]
    {L : ι → ℕ} (hj : ∀ j, L j=7 ∨ L j=3)
    (R : ProfileRow L 7) (S : ProfileRow L 3)
    (hcap : ∀ j, R.v j≤10) (hx : CrossMoment R S) : False := by
  have hR : (∑ j, L j * R.v j * R.v j)=98 := R.momentTwo
  have hS1 : (∑ j, L j * S.v j)=30 := S.momentOne
  have hS2 : (∑ j, L j * S.v j * S.v j)=30 := S.momentTwo
  have hs (j : ι) : S.v j ≤ 1 := by
    have hnon (i : ι) : L i * S.v i ≤ L i * S.v i * S.v i := by
      by_cases hz : S.v i=0
      · simp [hz]
      · simpa only [Nat.mul_one] using Nat.mul_le_mul_left (L i * S.v i)
          (show 1≤S.v i by omega)
    have ht : (∑ i, (L i*S.v i*S.v i-L i*S.v i))=0 := by
      rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hnon i), hS1, hS2]
    have hz := Finset.single_le_sum
      (f:=fun i : ι => L i*S.v i*S.v i-L i*S.v i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [ht] at hz
    by_contra! hbad
    have hp : 0 < L j * S.v j := by
      apply Nat.mul_pos
      · rcases hj j with he|he <;> omega
      · omega
    have hh := Nat.mul_le_mul_left (L j*S.v j) hbad
    omega
  have hall (j : ι) : L j * R.v j * S.v j=0 := by
    rcases hj j with he|he
    · have hb := S.block j
      rw [he] at hb
      have hsj := hs j
      have h0 : S.v j=0 := by omega
      simp [h0]
    · have hb := R.block j
      rw [he] at hb
      have hc := hcap j
      have hr : L j*R.v j*R.v j≤98 := by
        rw [←hR]
        exact Finset.single_le_sum (f:=fun i => L i*R.v i*R.v i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h0 : R.v j=0 ∨ R.v j=7 := by omega
      rcases h0 with h0|h0
      · simp [h0]
      · simp [h0,he] at hr
  change (∑ j, L j*R.v j*S.v j)=21 at hx
  simp only [hall,Finset.sum_const_zero] at hx
  omega

theorem no_three_seven_original_profile (F : OriginalProfileFacts
    (List.replicate 9 7 ++ List.replicate 10 3)) : False := by
  let P := List.replicate 9 7 ++ List.replicate 10 3
  have hj : ∀ j : Fin P.length, P.get j=7 ∨ P.get j=3 := by decide +kernel
  let r : Fin P.length := ⟨0, by decide⟩
  let s : Fin P.length := ⟨9, by decide⟩
  exact no_three_seven_cross_moment hj (F.row r) (F.row s)
    (F.cap r) (F.cross r s (by decide))

end Symconf93

#print axioms Symconf93.actual_incidence_profile
#print axioms Symconf93.physical_profile_mem_parity_free
#print axioms Symconf93.no_three_seven_original_profile
