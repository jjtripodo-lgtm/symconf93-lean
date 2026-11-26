module
public import Symconf59.CycleLayout
public import Symconf59.PermutationRegister
public import Symconf59.CycleCounts
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Orient each actual graph cycle, and recover exact common profile from
the two true matrix trace registers. -/
namespace Symconf59
open Matrix SimpleGraph Fin.NatCast
open scoped BigOperators Matrix

namespace CycleLayout
variable {V : Type*} {G : SimpleGraph V} (L : CycleLayout G)

noncomputable def move (n : ℕ) : Equiv.Perm (Σ c : G.ConnectedComponent,Fin (L.len c)) :=
  Equiv.sigmaCongrRight (fun c =>
    letI : NeZero (L.len c) := ⟨by have := L.minLen c; omega⟩
    Equiv.addRight (n:Fin (L.len c)))

noncomputable def rotation : Equiv.Perm V :=
  L.allSites.symm.trans ((L.move 1).trans L.allSites)

theorem rotation_forward (c : G.ConnectedComponent) (i : Fin (L.len c)) :
    L.rotation (L.allSites ⟨c,i⟩)=L.allSites ⟨c,cnext i⟩ := by
  change L.allSites (L.move 1 (L.allSites.symm (L.allSites ⟨c,i⟩)))=_
  rw [L.allSites.symm_apply_apply]
  rfl

theorem rotation_backward (c : G.ConnectedComponent) (i : Fin (L.len c)) :
    L.rotation⁻¹ (L.allSites ⟨c,i⟩)=L.allSites ⟨c,cprev i⟩ := by
  apply L.rotation.injective
  change L.rotation (L.rotation.symm (L.allSites ⟨c,i⟩))=_
  rw [L.rotation.apply_symm_apply,L.rotation_forward,cnext_prev]

theorem forward_ne_backward (x : V) : L.rotation x≠L.rotation⁻¹ x := by
  obtain ⟨⟨c,i⟩,rfl⟩ := L.allSites.surjective x
  rw [L.rotation_forward,L.rotation_backward]
  intro he
  exact next_prev_distinct (L.minLen c) i
    (eq_of_heq (Sigma.mk.inj_iff.mp (L.allSites.injective he)).2)

theorem adj_iff_rotation (x y : V) : G.Adj x y ↔ y=L.rotation x ∨ y=L.rotation⁻¹ x := by
  obtain ⟨⟨c,i⟩,rfl⟩ := L.allSites.surjective x
  obtain ⟨⟨d,j⟩,rfl⟩ := L.allSites.surjective y
  rw [L.rotation_forward,L.rotation_backward]
  by_cases hc : c=d
  · subst d
    change G.Adj (L.sites c i).val (L.sites c j).val ↔ _
    rw [L.adj]
    constructor
    · rintro (rfl|rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (he|he)
      · exact Or.inl (eq_of_heq (Sigma.mk.inj_iff.mp (L.allSites.injective he)).2)
      · exact Or.inr (eq_of_heq (Sigma.mk.inj_iff.mp (L.allSites.injective he)).2)
  · change G.Adj (L.sites c i).val (L.sites d j).val ↔ _
    constructor
    · exact fun h => False.elim (L.disjoint_component_adj hc i j h)
    · rintro (he|he)
      · exact False.elim (hc ((Sigma.mk.inj_iff.mp (L.allSites.injective he)).1.symm))
      · exact False.elim (hc ((Sigma.mk.inj_iff.mp (L.allSites.injective he)).1.symm))

theorem rotation_pow (c : G.ConnectedComponent) (i : Fin (L.len c)) (n : ℕ) :
    (L.rotation^n) (L.allSites ⟨c,i⟩)=L.allSites
      ⟨c,letI : NeZero (L.len c) := ⟨by have := L.minLen c; omega⟩
         i+(n:Fin (L.len c))⟩ := by
  letI : NeZero (L.len c) := ⟨by have := L.minLen c; omega⟩
  change (L.rotation^n) (L.allSites ⟨c,i⟩)=L.allSites ⟨c,i+(n:Fin (L.len c))⟩
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,L.rotation_forward,Nat.cast_succ,← add_assoc]
    rfl

theorem rotation_pow_fixed_iff (c : G.ConnectedComponent) (i : Fin (L.len c)) (n : ℕ) :
    (L.rotation^n) (L.allSites ⟨c,i⟩)=L.allSites ⟨c,i⟩ ↔ L.len c∣n := by
  letI : NeZero (L.len c) := ⟨by have := L.minLen c; omega⟩
  rw [L.rotation_pow]
  change L.allSites ⟨c,i+(n:Fin (L.len c))⟩=L.allSites ⟨c,i⟩ ↔ _
  have hfix : i+(n:Fin (L.len c))=i ↔ L.len c∣n := by
    rw [add_eq_left,Fin.natCast_eq_zero]
  constructor
  · intro h
    exact hfix.mp (eq_of_heq (Sigma.mk.inj_iff.mp (L.allSites.injective h)).2)
  · intro hd
    rw [hfix.mpr hd]

theorem fixed_signal [DecidableEq V] [Fintype V] [Fintype G.ConnectedComponent] (n : ℕ) :
    (∑ i : V,if (L.rotation^n) i=i then (1:ℤ) else 0)=
      ∑ c : G.ConnectedComponent, if L.len c∣n then (L.len c:ℤ) else 0 := by
  classical
  let f (i : V) : ℤ := if (L.rotation^n) i=i then 1 else 0
  change (∑i,f i)=_
  rw [← Equiv.sum_comp L.allSites f,Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [f,rotation_pow_fixed_iff]
  split_ifs <;> simp

end CycleLayout

theorem leave_matrix_from_rotation (M : Int59) (hd : ∀i,M i i=0)
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
theorem original_match_cycle_components {A : Int59} (hA : Incidence59 A) :
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

end Symconf59
