module
public import Symconf93.AffineGlobalJoin625
public import Symconf93.LiteralProfileAffine625
public import Symconf93.LiteralCyclicInverses93
public import Symconf93.GramCongruence93

@[expose] public section

namespace Symconf93.AffineFiber625
open Symconf59 Matrix
open scoped BigOperators Matrix
set_option maxHeartbeats 2000000

theorem gramNorm_eq_quad625 {ι : Type*} [Fintype ι] (m : Matrix ι ι (ZMod 625)) :
    gramNorm m=quad m := by
  funext x
  unfold gramNorm quad Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum,mul_assoc]

theorem rankOne_is_profileGram625 (P : List ℕ) :
    (withOnes (AffineCycle625.profileM P) : Matrix (BlocksOf P) (BlocksOf P) (ZMod 625)) =
      Symconf59.reduceMatrix 625 (profileGram93 P) := by
  ext i j
  simp only [withOnes,AffineCycle625.profileM,profileH93,Symconf59.reduceMatrix,
      Matrix.map_apply,map_sub,map_one]
  ring

theorem profile_stationary_is_kernel625 (P : List ℕ) (a : BlocksOf P→ZMod 25) :
    derivative (AffineCycle625.profileM P) (fun i=>lowCast (a i))=0 ↔
      action (fun i j=>lowReduce (AffineCycle625.profileM P i j)) a=0 := by
  rw [derivative_zero_iff_kernel]
  constructor
  · intro h; funext j
    change action (fun i j=>lowReduce (AffineCycle625.profileM P i j)) a j=0
    have e := h j
    simpa only [action,AffineCycle625.profileM_symmetric P,mul_comm] using e
  · intro h j
    have e := congrFun h j
    change action (fun i j=>lowReduce (AffineCycle625.profileM P i j)) a j=0 at e
    simpa only [action,AffineCycle625.profileM_symmetric P,mul_comm] using e

theorem literal_mod625_direct_contrast (i : Fin 23) :
    contrast (gramNorm (Symconf59.reduceMatrix 625 (profileGram93 (ModCount625.profile i))))
        (125 : ZMod 625) =
    (25 : ℤ)^93 * (5 * (-(5:ℤ)^(AffineCycle625.localExponent625 i))) := by
  erw [←rankOne_is_profileGram625,gramNorm_eq_quad625]
  let P := ModCount625.profile i
  have e := original_rank_one_contrast625 (ModCount625.actual_inverse i).totalSites
    (AffineCycle625.profileM P)
    (AffineCycle625.profileM_symmetric P) (AffineCycle625.profileM_rowSum P)
  have hs := AffineCycle625.literalProfileStationaryContrast625 i
  simp only [profile_stationary_is_kernel625] at hs
  unfold contrast
  rw [e, hs]

theorem no_integral_gram625_without_pivots (i : Fin 23) :
    ¬∃ A : Matrix (BlocksOf (ModCount625.profile i)) (BlocksOf (ModCount625.profile i)) ℤ,
      profileGram93 (ModCount625.profile i)=A*Aᵀ := by
  letI : Nonempty (BlocksOf (ModCount625.profile i)) := Fintype.card_pos_iff.mp (by
    rw [(ModCount625.actual_inverse i).totalSites];decide)
  have hneg : contrast (gramNorm (Symconf59.reduceMatrix 625
      (profileGram93 (ModCount625.profile i)))) (125:ZMod 625) < 0 := by
    rw [literal_mod625_direct_contrast]
    have hp : 0 < (5:ℤ)^(AffineCycle625.localExponent625 i) := pow_pos (by decide) _
    have hq : 0 < (25:ℤ)^93 := pow_pos (by decide) _
    exact mul_neg_of_pos_of_neg hq (mul_neg_of_pos_of_neg (by decide) (neg_lt_zero.mpr hp))
  exact no_integral_gram625_of_negative_contrast _ (ModCount625.actual_inverse i).clearedMatrix
    (700*ModCount625.invC i) (ModCount625.actual_inverse_nonzero i)
    (ModCount625.actual_inverse i).scaled_inverse (ModCount625.invW i:ZMod 625)
    (ModCount625.actual_inverse_modulus i) hneg

end Symconf93.AffineFiber625

#print axioms Symconf93.AffineFiber625.literal_mod625_direct_contrast
#print axioms Symconf93.AffineFiber625.no_integral_gram625_without_pivots
