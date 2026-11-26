module
public import Symconf59.CycleOrientation
public import Symconf93.CycleLayout
public import Symconf93.PermutationRegister
public import Symconf59.CycleCounts
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Orient each actual graph cycle, and recover exact common profile from
the two true matrix trace registers. -/
namespace Symconf93
open Symconf59
open Matrix
open scoped BigOperators Matrix

theorem leave_matrix_from_rotation (M : Int93) (hd : ∀i,M i i=0)
    (hs : Mᵀ=M) (hb : ∀i j,M i j=0 ∨ M i j=1)
    (L : CycleLayout (leaveGraph M hd hs)) : M=symmetricStep L.rotation 1 := by
  ext i j
  have h := L.adj_iff_rotation i j
  change M i j=1 ↔ j=L.rotation i ∨ j=L.rotation⁻¹ i at h
  simp only [symmetricStep,pow_one,Matrix.add_apply,permMat]
  rcases hb i j with he|he
  · have hn : ¬(j=L.rotation i ∨ j=L.rotation⁻¹ i) := by
      intro hf
      have hh := h.mpr hf
      omega
    rw [he,if_neg (not_or.mp hn).1,if_neg (not_or.mp hn).2,add_zero]
  · rcases h.mp he with hf|hf
    · have hg : j≠L.rotation⁻¹ i := hf.symm ▸ L.forward_ne_backward i
      rw [he,if_pos hf,if_neg hg,add_zero]
    · have hg : j≠L.rotation i := hf.symm ▸ (L.forward_ne_backward i).symm
      rw [he,if_neg hg,if_pos hf,zero_add]

/-- Both observed leaves of the original incidence matrix have exactly the
same cycle lengths, matched by a bijection of their actual components. -/
theorem original_match_cycle_components {A : Int93} (hA : Incidence93 A) :
    ∃ e : (leaveGraph (rowLeave A) (rowLeave_diag hA) (rowLeave_symm A)).ConnectedComponent ≃
        (leaveGraph (rowLeave Aᵀ) (rowLeave_diag hA.transpose) (rowLeave_symm Aᵀ)).ConnectedComponent,
      ∀ c, (originalRowLayout hA.transpose).len (e c)=(originalRowLayout hA).len c := by
  classical
  let L := originalRowLayout hA
  let R := originalRowLayout hA.transpose
  letI : Fintype (leaveGraph (rowLeave A) (rowLeave_diag hA) (rowLeave_symm A)).ConnectedComponent :=
    Fintype.ofFinite _
  letI : Fintype (leaveGraph (rowLeave Aᵀ) (rowLeave_diag hA.transpose) (rowLeave_symm Aᵀ)).ConnectedComponent :=
    Fintype.ofFinite _
  have h1 := leave_matrix_from_rotation (rowLeave A) _ _ (rowLeave_binary hA) L
  have h2 := leave_matrix_from_rotation (colLeave A) _ _ (rowLeave_binary hA.transpose) R
  have hf := original_power_fixed_counts hA L.rotation R.rotation h1 h2
  apply match_cycle_lengths L.len R.len
  intro n
  by_cases hn : 0<n
  · apply divisorScore_injective_off_zero _ _ _ n hn
    intro k hk
    rw [cycle_weighted_divisor_score L.len k hk,cycle_weighted_divisor_score R.len k hk]
    have hcast := hf k
    rw [L.fixed_signal,R.fixed_signal] at hcast
    exact_mod_cast hcast
  · have hz : n=0 := by omega
    subst n
    have hL : (Finset.univ.filter (fun c => L.len c=0))=∅ := by
      ext c
      have hv : L.len c≠0 := by have := L.minLen c; omega
      simp [hv]
    have hR : (Finset.univ.filter (fun c => R.len c=0))=∅ := by
      ext c
      have hv : R.len c≠0 := by have := R.minLen c; omega
      simp [hv]
    simp [lengthCount,hL,hR]

end Symconf93
