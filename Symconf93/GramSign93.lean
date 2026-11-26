module
public import Symconf93.NormCountTransport
public import Symconf59.GramObstruction
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-! Elementary Gram obstruction from the exact finite modular contrasts. -/
namespace Symconf93
open Matrix
open scoped BigOperators Matrix

section Abstract
variable {ι R S : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [CommRing R] [Finite R] [AddGroup S] [DecidableEq S]

def gramNorm (G : Matrix ι ι R) (x : ι → R) : R :=
  x ⬝ᵥ (G *ᵥ x)

noncomputable def contrast (q : (ι → R) → R) (t : R) : ℤ :=
  (Nat.card {v : ι → R // q v=0}:ℤ) - Nat.card {v : ι → R // q v=t}

omit [Nonempty ι] [DecidableEq ι] [Finite R] in
theorem gramNorm_of_factor (A : Matrix ι ι R) (x : ι → R) :
    gramNorm (A*Aᵀ) x=coordinateNorm (Aᵀ *ᵥ x) := by
  unfold gramNorm coordinateNorm
  rw [← mulVec_mulVec]
  simpa only [transpose_transpose,dotProduct] using
    (Matrix.dotProduct_transpose_mulVec Aᵀ x (Aᵀ *ᵥ x))

/-- A certified scaled image and a certified low-digit shift transport
the sign of the identity norm contrast to any finite Gram factor. -/
theorem gram_contrast_nonneg_of_scaled_image
    (A M : Matrix ι ι R) (a : R) (hA : Aᵀ*M=a • (1:Matrix ι ι R))
    (c : R →+ S) (step : S → R) (t : R)
    (hTag : ∀ x:R, c x=0 → ∃ y, x=a*y)
    (hStep : ∀ b, c (step b)=0)
    (hCross : ∀ x:R, c x≠0 → 2*x*step (c x)+step (c x)*step (c x)=t)
    (hI : 0≤contrast (coordinateNorm (ι:=ι)) t) :
    0≤contrast (gramNorm (A*Aᵀ)) t := by
  classical
  let f : (ι→R) →+ (ι→R) := (Matrix.mulVecLin Aᵀ).toAddMonoidHom
  let L : AddSubgroup (ι→R) :=
    { carrier := Set.range f
      zero_mem' := ⟨0,map_zero f⟩
      add_mem' := by
        rintro _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
        exact ⟨u+v,map_add f u v⟩
      neg_mem' := by
        rintro _ ⟨u,rfl⟩
        exact ⟨-u,map_neg f u⟩ }
  have hcontain (v : ι→R) (hv : ∀ i,c (v i)=0) : v∈L := by
    choose w hw using fun i => hTag (v i) (hv i)
    refine ⟨M *ᵥ w,?_⟩
    change Aᵀ *ᵥ (M *ᵥ w)=v
    rw [mulVec_mulVec,hA,smul_mulVec,one_mulVec]
    ext i
    exact (hw i).symm
  have eq := signed_norm_count_transport f coordinateNorm 0 t
    (complement_norm_fibers_equiv L c hcontain step hStep t hCross)
  change contrast ((coordinateNorm (ι:=ι)) ∘ f) t =
      (Nat.card {v : ι→R // f v=0}:ℤ)*contrast (coordinateNorm (ι:=ι)) t at eq
  have he : gramNorm (A*Aᵀ) = coordinateNorm ∘ f := funext (gramNorm_of_factor A)
  rw [he,eq]
  exact mul_nonneg (by positivity) hI

end Abstract

section Integral
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rational-inverse observation proved by the integral adjugate.
It gives the appropriate side of the image, not the image of A. -/
theorem gram_integral_right_scale (A B : Matrix ι ι ℤ) (d : ℤ) (hd : d≠0)
    (hB : B*(A*Aᵀ)=d • (1:Matrix ι ι ℤ)) :
    Aᵀ*(B*A)=d • (1:Matrix ι ι ℤ) := by
  have hab : (B*A)*Aᵀ=d • (1:Matrix ι ι ℤ) := by
    simpa only [mul_assoc] using hB
  have hz : Aᵀ.det≠0 := by
    intro he
    have hs := congrArg Matrix.det hab
    rw [Matrix.det_mul,he,mul_zero,Matrix.det_smul,Matrix.det_one,mul_one] at hs
    exact (pow_ne_zero _ hd) hs.symm
  have he : (Aᵀ*(B*A))*Aᵀ=(d • (1:Matrix ι ι ℤ))*Aᵀ := by
    rw [mul_assoc,hab,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  have ht := congrArg (fun M : Matrix ι ι ℤ => M * Aᵀ.adjugate) he
  simp only [mul_assoc, Matrix.mul_adjugate, mul_smul_comm,mul_one] at ht
  ext i j
  have hh := congrArg (fun M : Matrix ι ι ℤ => M i j) ht
  simp only [Matrix.smul_apply,smul_eq_mul] at hh
  exact mul_left_cancel₀ hz hh

theorem integer_gram_has_reduced_scaled_image (q : ℕ)
    (G A B : Matrix ι ι ℤ) (d : ℤ) (hd : d≠0)
    (hG : G=A*Aᵀ) (hB : B*G=d • (1:Matrix ι ι ℤ))
    (s w : ZMod q) (hw : w*(d:ZMod q)=s) :
    ∃ M : Matrix ι ι (ZMod q), (Symconf59.reduceMatrix q A)ᵀ*M=
      s • (1:Matrix ι ι (ZMod q)) := by
  rw [hG] at hB
  have hi := gram_integral_right_scale A B d hd hB
  let F : Matrix ι ι ℤ →+* Matrix ι ι (ZMod q) :=
    (Int.castRingHom (ZMod q)).mapMatrix
  have hm := congrArg F hi
  rw [map_mul,map_mul] at hm
  have hOne : F (d • (1:Matrix ι ι ℤ))=(d:ZMod q) • (1:Matrix ι ι (ZMod q)) := by
    ext i j
    change ((d*(1:Matrix ι ι ℤ) i j : ℤ):ZMod q)=(d:ZMod q)*(1:Matrix ι ι (ZMod q)) i j
    rw [Int.cast_mul]
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  rw [hOne] at hm
  refine ⟨w • (F B*F A),?_⟩
  change F Aᵀ*(w • (F B*F A))=_
  rw [mul_smul_comm,hm,smul_smul,hw]

end Integral
end Symconf93

#print axioms Symconf93.gram_contrast_nonneg_of_scaled_image
#print axioms Symconf93.gram_integral_right_scale
#print axioms Symconf93.integer_gram_has_reduced_scaled_image
