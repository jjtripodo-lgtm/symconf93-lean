module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Ring

@[expose] public section

/-! A lattice obstruction to a square integral Gram factorization.
The chosen integer lift of a modular vector in the kernel of the
transposed factor is already divisible in every physical coordinate. -/

namespace Symconf59
open Matrix
open scoped Matrix BigOperators

variable {n : Type*} [Fintype n]

def reduceMatrix (p : ℕ) (M : Matrix n n ℤ) : Matrix n n (ZMod p) :=
  M.map (Int.castRingHom (ZMod p))

def reduceVec (p : ℕ) (v : n → ℤ) : n → ZMod p :=
  fun i => (v i : ZMod p)

theorem reduce_mulVec (p : ℕ) (M : Matrix n n ℤ) (v : n → ℤ) :
    reduceVec p (M *ᵥ v)=reduceMatrix p M *ᵥ reduceVec p v :=
  funext fun i => RingHom.map_mulVec (Int.castRingHom (ZMod p)) M v i

def gramPair (G : Matrix n n ℤ) (x y : n → ℤ) : ℤ :=
  x ⬝ᵥ (G *ᵥ y)

theorem gramPair_combo (G : Matrix n n ℤ) (u v : n → ℤ) (a b : ℤ) :
    gramPair G (a • u+b • v) (a • u+b • v) =
      a*a*gramPair G u u+a*b*gramPair G u v+
        b*a*gramPair G v u+b*b*gramPair G v v := by
  unfold gramPair
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- The square norm has a full extra factor of p, not merely mod-p zero. -/
theorem square_divisibility_of_reduce_transpose_zero (p : ℕ)
    (A : Matrix n n ℤ) (x : n → ℤ)
    (hx : reduceMatrix p Aᵀ *ᵥ reduceVec p x=0) :
    ((p : ℤ)*(p : ℤ)) ∣ gramPair (A*Aᵀ) x x := by
  classical
  have hh : ∀ i, (p : ℤ) ∣ (Aᵀ *ᵥ x) i := by
    intro i
    have he := congrFun ((reduce_mulVec p Aᵀ x).trans hx) i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  choose z hz using hh
  have hrepr : Aᵀ *ᵥ x=(p : ℤ) • z := funext hz
  refine ⟨z ⬝ᵥ z,?_⟩
  unfold gramPair
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.transpose_transpose A,
    Matrix.vecMul_transpose, Matrix.transpose_transpose, hrepr,smul_dotProduct,dotProduct_smul,
    smul_eq_mul,smul_eq_mul]
  ring

/-- Basis values are quotients with exact divisibility certificates, not
uninterpreted division. A nonzero radical and its complete two-generator
description suffice. Choose exactly a lifted combination of those generators
for the nonzero modular vector in the kernel of the transposed factor. -/
theorem no_integral_gram_of_anisotropic_pair [DecidableEq n] (p : ℕ) [Fact (Nat.Prime p)]
    (G : Matrix n n ℤ) (u v : n → ℤ) (b11 b12 b21 b22 : ℤ)
    (hnz : ∃ x : n → ZMod p, x≠0 ∧ reduceMatrix p G *ᵥ x=0)
    (hspan : ∀ x : n → ZMod p, reduceMatrix p G *ᵥ x=0 →
      ∃ a b : ZMod p, x=a • reduceVec p u+b • reduceVec p v)
    (huu : gramPair G u u=(p : ℤ)*b11)
    (huv : gramPair G u v=(p : ℤ)*b12)
    (hvu : gramPair G v u=(p : ℤ)*b21)
    (hvv : gramPair G v v=(p : ℤ)*b22)
    (haniso : ∀ a b : ZMod p,
      a*a*(b11 : ZMod p)+a*b*(b12 : ZMod p)+b*a*(b21 : ZMod p)+b*b*(b22 : ZMod p)=0 →
      a=0 ∧ b=0) :
    ¬ ∃ A : Matrix n n ℤ, G=A*Aᵀ := by
  rintro ⟨A,hA⟩
  let M := reduceMatrix p A
  have hT : reduceMatrix p Aᵀ=Mᵀ := rfl
  have hG : reduceMatrix p G=M*Mᵀ := by
    rw [hA]
    change Matrix.map (A*Aᵀ) (Int.castRingHom (ZMod p))=_
    rw [Matrix.map_mul]
    change M*reduceMatrix p Aᵀ=_
    rw [hT]
  have hNI : ¬Function.Injective (Mᵀ).mulVec := by
    intro hinj
    have huM := (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_transpose M).mp ((Matrix.mulVec_injective_iff_isUnit).mp hinj))
    obtain ⟨x,hx,hh⟩ := hnz
    rw [hG,← Matrix.mulVec_mulVec] at hh
    have ht : Mᵀ *ᵥ x=0 := huM (hh.trans (Matrix.mulVec_zero M).symm)
    exact hx (hinj (ht.trans (Matrix.mulVec_zero Mᵀ).symm))
  obtain ⟨a₀,b₀,heq,hne⟩ := Function.not_injective_iff.mp hNI
  let x := a₀-b₀
  have hx : x≠0 := sub_ne_zero.mpr hne
  have hMx : Mᵀ *ᵥ x=0 := by
    change Mᵀ *ᵥ (a₀-b₀)=0
    rw [Matrix.mulVec_sub,heq,sub_self]
  have hGx : reduceMatrix p G *ᵥ x=0 := by
    rw [hG,← Matrix.mulVec_mulVec,hMx,Matrix.mulVec_zero]
  obtain ⟨a,b,hab⟩ := hspan x hGx
  let ac : ℤ := ZMod.cast a
  let bc : ℤ := ZMod.cast b
  have hac : (ac : ZMod p)=a := ZMod.intCast_zmod_cast a
  have hbc : (bc : ZMod p)=b := ZMod.intCast_zmod_cast b
  let k := ac • u+bc • v
  have hk : reduceVec p k=x := by
    rw [hab]
    funext i
    change ((ac*u i+bc*v i : ℤ) : ZMod p)=a*(u i : ZMod p)+b*(v i : ZMod p)
    rw [Int.cast_add,Int.cast_mul,Int.cast_mul,hac,hbc]
  have hzero : reduceMatrix p Aᵀ *ᵥ reduceVec p k=0 := by rw [hT,hk,hMx]
  obtain ⟨q,hq⟩ := square_divisibility_of_reduce_transpose_zero p A k hzero
  have hq' : gramPair G k k=(p : ℤ)*(p : ℤ)*q := hA ▸ hq
  let N := ac*ac*b11+ac*bc*b12+bc*ac*b21+bc*bc*b22
  have hN : gramPair G k k=(p : ℤ)*N := by
    change gramPair G (ac • u+bc • v) (ac • u+bc • v)=_
    rw [gramPair_combo,huu,huv,hvu,hvv]
    dsimp [N]
    ring
  have hp : (p : ℤ)≠0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have he : N=(p : ℤ)*q :=
    mul_left_cancel₀ hp (hN.symm.trans (hq'.trans (mul_assoc _ _ _)))
  have he' : (N : ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨q,he⟩
  have heMod : a*a*(b11 : ZMod p)+a*b*(b12 : ZMod p)+b*a*(b21 : ZMod p)+b*b*(b22 : ZMod p)=0 := by
    simpa only [N,Int.cast_add,Int.cast_mul,hac,hbc] using he'
  obtain ⟨h₁,h₂⟩ := haniso a b heMod
  apply hx
  rw [hab,h₁,h₂,zero_smul,zero_smul,add_zero]

end Symconf59
