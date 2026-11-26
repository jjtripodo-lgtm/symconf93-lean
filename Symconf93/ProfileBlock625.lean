module
public import Symconf93.StationaryCycleNorm625

@[expose] public section

/-! Exact block decomposition of the original H=G−J, not of a surrogate
Gram or of an independently enumerated reordered profile. -/
namespace Symconf93.AffineCycle625
open AffineFiber625 Matrix
open scoped BigOperators Matrix

def profileM (P : List ℕ) : BlocksOf P→BlocksOf P→ZMod 625 :=
  (profileH93 P).map (Int.castRingHom (ZMod 625))

theorem profileM_same (P : List ℕ) (b : Fin P.length) (i j : Fin (P.get b)) :
    profileM P ⟨b,i⟩ ⟨b,j⟩=cycleM (P.get b) i j := by
  have h : profileH93 P ⟨b,i⟩ ⟨b,j⟩=cycleH93 (P.get b) i j := by
    simp only [profileH93,profileGram93,profileAdj93,cycleH93,Sigma.mk.inj_iff,heq_eq_eq,true_and]
    ring
  exact congrArg (Int.castRingHom (ZMod 625)) h

theorem profileM_off (P : List ℕ) (a b : Fin P.length) (h : a≠b)
    (i : Fin (P.get a)) (j : Fin (P.get b)) :
    profileM P ⟨a,i⟩ ⟨b,j⟩=0 := by
  have he {z : Fin (P.get a)} : (⟨b,j⟩:BlocksOf P)≠⟨a,z⟩ := by
    intro hz
    exact h.symm (congrArg Sigma.fst hz)
  have hne : (⟨a,i⟩:BlocksOf P)≠⟨b,j⟩ := (he (z:=i)).symm
  have ho : profileH93 P ⟨a,i⟩ ⟨b,j⟩=0 := by
    simp [profileH93,profileGram93,profileAdj93,he,hne]
  change ((profileH93 P ⟨a,i⟩ ⟨b,j⟩:ℤ):ZMod 625)=0
  rw [ho,Int.cast_zero]

theorem profileM_symmetric (P : List ℕ) :
    ∀ i j, profileM P i j=profileM P j i := by
  rintro ⟨a,i⟩ ⟨b,j⟩
  by_cases h : a=b
  · subst b
    rw [profileM_same,profileM_same]
    exact cycleM_symmetric _ i j
  · rw [profileM_off P a b h,profileM_off P b a (Ne.symm h)]

theorem profileM_rowSum (P : List ℕ) :
    ∀ i, (∑ j,profileM P i j)=7 := by
  rintro ⟨a,i⟩
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single a]
  · simp_rw [profileM_same]
    have hi : (∑ j, cycleH93 (P.get a) i j)=7 := by
      simp [cycleH93,Finset.sum_sub_distrib]
    have hM := congrArg (Int.castRingHom (ZMod 625)) hi
    simpa only [map_sum,cycleM,Matrix.map_apply,map_ofNat] using hM
  · intro b _ hb
    simp [profileM_off P a b hb.symm]
  · simp

theorem profileH_stationary_iff (P : List ℕ) (a : BlocksOf P→ZMod 25) :
    derivative (profileM P) (fun i=>lowCast (a i))=0 ↔
      ∀ b : Fin P.length, rowEq (fun i : Fin (P.get b) => a ⟨b,i⟩) := by
  rw [derivative_zero_iff_kernel]
  have eqb (b : Fin P.length) (j : Fin (P.get b)) :
      (∑ i : BlocksOf P, a i*lowReduce (profileM P i ⟨b,j⟩)) =
        9*a ⟨b,j⟩-a ⟨b,Symconf59.cnext j⟩-a ⟨b,Symconf59.cprev j⟩ := by
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single b]
    · simp_rw [profileM_same,cycleM_symmetric (P.get b) _ j]
      have hline (i : Fin (P.get b)) :
          a ⟨b,i⟩*lowReduce (cycleM (P.get b) j i) =
            (((cycleH93 (P.get b)).map (Int.castRingHom (ZMod 25))) j i)*a ⟨b,i⟩ := by
        change a ⟨b,i⟩*lowReduce (((cycleH93 (P.get b) j i:ℤ):ZMod 625)) =
          ((cycleH93 (P.get b) j i:ℤ):ZMod 25)*a ⟨b,i⟩
        rw [map_intCast,mul_comm]
      simp_rw [hline]
      change ((((cycleH93 (P.get b)).map (Int.castRingHom (ZMod 25))) *ᵥ
        (fun i : Fin (P.get b) => a ⟨b,i⟩)) j)=_
      rw [cycleH_action]
    · intro b' _ hb'
      simp [profileM_off P b' b hb']
    · simp
  constructor
  · intro h b j
    rw [←eqb b j]
    exact h ⟨b,j⟩
  · rintro h ⟨b,j⟩
    rw [eqb b j]
    exact h b j

theorem profileH_norm_blocks (P : List ℕ) (x : BlocksOf P→ZMod 625) :
    quad (profileM P) x =
      ∑ b : Fin P.length, quad (cycleM (P.get b)) (fun i => x ⟨b,i⟩) := by
  unfold quad
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp_rw [profileM_same]
  · intro b' _ hb'
    simp [profileM_off P b b' hb'.symm]
  · simp

def ProfileKernel (P : List ℕ) :=
  {a : BlocksOf P→ZMod 25 // derivative (profileM P) (fun i=>lowCast (a i))=0}

def CycleKernel (n : ℕ) :=
  {a : Fin n→ZMod 25 // rowEq a}


noncomputable instance (P : List ℕ) : Fintype (ProfileKernel P) := by
  unfold ProfileKernel
  exact Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (CycleKernel n) := by
  unfold CycleKernel
  exact Fintype.ofFinite _

def profileKernel_blocks_equiv (P : List ℕ) :
    ProfileKernel P ≃ ((b : Fin P.length) → CycleKernel (P.get b)) where
  toFun x b := ⟨fun i=>x.val ⟨b,i⟩, (profileH_stationary_iff P _).mp x.property b⟩
  invFun y := ⟨fun i=> (y i.1).val i.2,
    (profileH_stationary_iff P _).mpr (fun b=>(y b).property)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i
    rfl
  right_inv y := by
    funext b
    apply Subtype.ext
    rfl

def profileKernelQuad (P : List ℕ) (x : ProfileKernel P) : ZMod 625 :=
  quad (profileM P) (fun i=>lowCast (x.val i))

theorem profileKernelQuad_blocks (P : List ℕ) (x : ProfileKernel P) :
    profileKernelQuad P x =
      ∑ b, stationaryCycleQuad (P.get b) ((profileKernel_blocks_equiv P) x b) :=
  profileH_norm_blocks P _

end Symconf93.AffineCycle625
#print axioms Symconf93.AffineCycle625.profileKernel_blocks_equiv
#print axioms Symconf93.AffineCycle625.profileKernelQuad_blocks

#print axioms Symconf93.AffineCycle625.profileM_rowSum
