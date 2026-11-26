module
public import Symconf93.NormCountTransport
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Literal modular quadratic-form counts by convolution, with certified
compression under multiplying a target residue by a unit square. -/
namespace Symconf93
open scoped BigOperators

section Ring
variable {R : Type*} [CommRing R]

def diagonalNorm {n : ℕ} (D : Fin n → R) (x : Fin n → R) : R :=
  ∑ i, D i * x i * x i

noncomputable def diagonalCount {n : ℕ} (D : Fin n → R) (t : R) : ℕ :=
  Nat.card {x : Fin n → R // diagonalNorm D x=t}

private theorem diag_cons {n : ℕ} (D : Fin (n+1) → R) (x : Fin n → R) (b : R) :
    diagonalNorm D (Fin.cons b x)=D 0*b*b+
      diagonalNorm (fun i => D i.succ) x := by
  simp only [diagonalNorm,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

/-- Add one independent coordinate: every term counts a genuine fiber
of the previous literal quadratic form. -/
theorem diagonalCount_succ [Fintype R] {n : ℕ} (D : Fin (n+1) → R) (t : R) :
    diagonalCount D t = ∑ b : R, diagonalCount (fun i => D i.succ)
      (t-D 0*b*b) := by
  classical
  let F (b : R) := {x : Fin n → R // diagonalNorm (fun i => D i.succ) x=t-D 0*b*b}
  letI (b : R) : Fintype (F b) := Fintype.ofFinite _
  let E : {x : Fin (n+1) → R // diagonalNorm D x=t} ≃ Σ b:R,F b :=
    { toFun := fun x => ⟨x.val 0,⟨Fin.tail x.val,by
        have h := x.property
        rw [← Fin.cons_self_tail x.val,diag_cons] at h
        exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)⟩⟩
      invFun := fun bx => ⟨Fin.cons bx.1 bx.2.val,by
        rw [diag_cons,bx.2.property]
        ring⟩
      left_inv := by intro x; apply Subtype.ext; exact Fin.cons_self_tail x.val
      right_inv := by
        rintro ⟨b,x⟩
        have hb : (Fin.cons (α:=fun _=>R) b x.val) 0=b := by simp only [Fin.cons_zero]
        refine Sigma.ext hb ?_
        simp only [Fin.tail_cons]
        rfl }
  unfold diagonalCount
  rw [Nat.card_congr E, Nat.card_eq_fintype_card,Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card,F]

theorem diagonalCount_zero [DecidableEq R] (D : Fin 0 → R) (t : R) :
    diagonalCount D t = if t=0 then 1 else 0 := by
  classical
  unfold diagonalCount
  by_cases h : t=0
  · subst t
    let x : Fin 0 → R := Fin.elim0
    have hn : diagonalNorm D x=0 := by simp [diagonalNorm]
    haveI : Unique {x : Fin 0 → R // diagonalNorm D x=0} :=
      { default := ⟨x,hn⟩
        uniq := fun f => Subtype.ext (funext fun i => i.elim0) }
    simp
  · haveI : IsEmpty {x : Fin 0 → R // diagonalNorm D x=t} :=
      ⟨by rintro ⟨x,hx⟩; apply h; simpa [diagonalNorm] using hx.symm⟩
    simp [h]

theorem diagonalCount_unit_square {n : ℕ} (D : Fin n → R) (t : R) (u : Rˣ) :
    diagonalCount D t = diagonalCount D ((u:R)*(u:R)*t) := by
  let E : (Fin n → R) ≃ (Fin n → R) :=
    { toFun := fun x i => (u:R)*x i
      invFun := fun x i => (↑u⁻¹:R)*x i
      left_inv := by intro x; funext i; simp [← mul_assoc]
      right_inv := by intro x; funext i; simp [← mul_assoc] }
  have hn (x : Fin n → R) :
      diagonalNorm D (E x)=(u:R)*(u:R)*diagonalNorm D x := by
    unfold diagonalNorm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change D i*((u:R)*x i)*((u:R)*x i)=_
    ring
  unfold diagonalCount
  apply Nat.card_congr (Equiv.subtypeEquiv E (fun x => ?_))
  rw [hn]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg (fun v : R => (↑u⁻¹:R)*(↑u⁻¹:R)*v) h
    have he : (↑u⁻¹:R)*(↑u⁻¹:R)*((u:R)*(u:R))=1 := by
      calc
        _ = ((↑u⁻¹:R)*(u:R))*((↑u⁻¹:R)*(u:R)) := by ring
        _ = _ := by simp
    simpa only [← mul_assoc,he,one_mul] using h'

/-- It is enough to retain one exact count per square-unit orbit. -/
theorem diagonalCount_on_selected_orbit {n : ℕ} {K : Type*} (D : Fin n → R)
    (cl : R → K) (rep : K → R)
    (hcl : ∀ t, ∃ u : Rˣ, t=(u:R)*(u:R)*rep (cl t)) (t : R) :
    diagonalCount D t = diagonalCount D (rep (cl t)) := by
  obtain ⟨u,hu⟩ := hcl t
  have h := diagonalCount_unit_square D (rep (cl t)) u
  rw [← hu] at h
  exact h.symm

end Ring
end Symconf93

#print axioms Symconf93.diagonalCount_succ
#print axioms Symconf93.diagonalCount_unit_square
#print axioms Symconf93.diagonalCount_on_selected_orbit
