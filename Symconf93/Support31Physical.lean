module
public import Symconf93.TwoBankNormalize
public import Mathlib.Data.Finset.Prod

@[expose] public section

/-! Literal support pairs, not just abstruse autocorrelation symbols. -/
namespace Symconf93
open scoped BigOperators

def support31 (f : Z31→ℤ) : Finset Z31 :=
  Finset.univ.filter (fun z => f z=1)

def residuePairs31 (f g : Z31→ℤ) (d : Z31) : Finset (Z31×Z31) :=
  ((support31 f) ×ˢ (support31 g)).filter (fun ab => ab.2-ab.1=d)

theorem support31_card {f : Z31→ℤ} (hb : ∀ z, f z=0 ∨ f z=1) :
    ((support31 f).card:ℤ)=∑z,f z := by
  have h (z : Z31) : f z=(if f z=1 then 1 else 0 : ℤ) := by
    rcases hb z with h|h <;> simp [h]
  conv_rhs => arg 2; ext z; rw [h]
  rw [← Finset.sum_filter]
  simp [support31]

/-- Exact signed cross support distances, counting every pair with its
multiplicity. Thus equal autocorrelations are the literal two-shore gap data. -/
theorem cycleCorr31_literal_pairs {f g : Z31→ℤ}
    (hf : ∀ z, f z=0 ∨ f z=1) (hg : ∀ z,g z=0 ∨ g z=1) (d : Z31) :
    cycleCorr31 f g d=((residuePairs31 f g d).card:ℤ) := by
  classical
  let A : Finset Z31 := Finset.univ.filter (fun z => f (z-d)=1 ∧ g z=1)
  have hsum : cycleCorr31 f g d=(A.card:ℤ) := by
    unfold cycleCorr31
    have h (z : Z31) : f (z-d)*g z=(if f (z-d)=1 ∧ g z=1 then 1 else 0:ℤ) := by
      rcases hf (z-d) with h|h <;> rcases hg z with h'|h' <;> simp [h,h']
    simp only [h,←Finset.sum_filter,A,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hsum]
  congr 1
  apply Finset.card_bij (fun z _ => (z-d,z))
  · intro z hz
    have ha : f (z-d)=1 ∧ g z=1 := by simpa [A] using hz
    simp [residuePairs31,support31,ha,sub_sub_cancel]
  · intro z _ w _ h
    exact congrArg Prod.snd h
  · intro p hp
    rcases p with ⟨a,b⟩
    have hh : (f a=1 ∧ g b=1) ∧ b-a=d := by
      simpa [residuePairs31,support31] using hp
    have he : b-d=a := by rw [←hh.2,sub_sub_cancel]
    refine ⟨b,?_ ,?_⟩
    · simp [A,he,hh.1]
    · simp only [he]

def translatedSupport31 (f : Z31→ℤ) (a : Z31) (z : Z31) : ℤ := f (z-a)

theorem cycleCorr31_translate (f g : Z31→ℤ) (a b d : Z31) :
    cycleCorr31 (translatedSupport31 f a) (translatedSupport31 g b) d=
      cycleCorr31 f g (d+a-b) := by
  unfold cycleCorr31 translatedSupport31
  have h := Equiv.sum_comp (Equiv.addRight b) (fun z=>f (z-d-a)*g (z-b))
  calc
    _ = ∑ z : Z31, f (z+b-d-a)*g (z+b-b) := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [add_sub_cancel_right]
      congr 2
      ring

theorem normalize_one_support31 (f : Z31→ℤ) (hf : ∀ z, f z=0 ∨ f z=1)
    (hpos : 0<∑ z,f z) :
    ∃ w:Z31, translatedSupport31 f w 0=1 ∧
      (∀ d, cycleAuto31 (translatedSupport31 f w) d=cycleAuto31 f d) := by
  have hn : (support31 f).Nonempty := by
    rw [←Finset.card_pos]
    have h := support31_card hf
    exact_mod_cast (h.symm ▸ hpos)
  obtain ⟨z,hz⟩ := hn
  have he : f z=1 := by simpa [support31] using hz
  refine ⟨-z,?_ ,?_⟩
  · simpa [translatedSupport31] using he
  · intro d
    unfold cycleAuto31
    rw [cycleCorr31_translate,add_sub_cancel_right]

/-- A complete rooted cross cover is unchanged by translating just one
whole bank, so computing with the first relative phase zero is sound. -/
theorem fixed_cross_cover_global_shift (B : FixedBanks31) (t : Z31) (d : Z31) :
    (∑j,cycleCorr31 (B.f j) (translatedSupport31 (B.g j) t) d)=1 := by
  have h (j : Fin 3) : translatedSupport31 (B.f j) 0=B.f j := by
    funext z
    simp [translatedSupport31]
  calc
    _ = ∑ j,cycleCorr31 (B.f j) (B.g j) (d-t) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [←h j,cycleCorr31_translate,h j,add_zero]
    _ = 1 := B.mixed_cover (d-t)

end Symconf93

#print axioms Symconf93.cycleCorr31_literal_pairs
#print axioms Symconf93.cycleCorr31_translate
#print axioms Symconf93.normalize_one_support31
