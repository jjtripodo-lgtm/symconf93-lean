module
public import Symconf93.ValidNatSupport31
public import Symconf93.LocalCatalogSound
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Recover a normalized, strictly ordered, literal 31-cycle support from
the actual binary physical function. -/
namespace Symconf93
open scoped BigOperators

def sortedSupport31 (f : Z31→ℤ) : List Nat :=
  ((support31 f).image ZMod.val).sort

theorem member_sortedSupport31 (f : Z31→ℤ) (a : Nat) :
    a∈sortedSupport31 f ↔ a<31 ∧ f (a:Z31)=1 := by
  unfold sortedSupport31
  rw [Finset.mem_sort,Finset.mem_image]
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨ZMod.val_lt z,by simpa only [ZMod.natCast_zmod_val] using
      (Finset.mem_filter.mp hz).2⟩
  · rintro ⟨ha,hg⟩
    refine ⟨(a:Z31), Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩,?_⟩
    exact ZMod.val_natCast_of_lt ha

theorem length_sortedSupport31 (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1)
    (k : Nat) (hk : (∑z,f z)=(k:ℤ)) : (sortedSupport31 f).length=k := by
  rw [sortedSupport31,Finset.length_sort,Finset.card_image_of_injective _ (ZMod.val_injective 31)]
  exact_mod_cast (support31_card hf |>.trans hk)

theorem normalization_input31 (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1) (k : Nat)
    (hk2 : 2≤k) (hk : (∑z,f z)=(k:ℤ)) (h0 : f 0=1) :
    ∃ u : Fin 31, 0<u.val ∧ sortedSupport31 f∈normalizedFirst31 k u.val := by
  have hLen := length_sortedSupport31 f hf k hk
  have hSort : (sortedSupport31 f).Pairwise (·<·) :=
    (Finset.sortedLT_sort ((support31 f).image ZMod.val)).pairwise
  have hz : 0∈sortedSupport31 f := (member_sortedSupport31 f 0).mpr ⟨by decide,h0⟩
  cases hL : sortedSupport31 f with
  | nil => simp [hL] at hz
  | cons a S =>
    rw [hL] at hLen hSort hz
    have ha : a=0 := by
      rcases List.mem_cons.mp hz with hh|hh
      · exact hh.symm
      · have hneg := (List.pairwise_cons.mp hSort).1 0 hh
        omega
    subst a
    cases S with
    | nil =>
      simp only [List.length_cons,List.length_nil] at hLen
      omega
    | cons u L =>
      have hTail := (List.pairwise_cons.mp hSort).2
      have hu : 0<u := (List.pairwise_cons.mp hSort).1 u (by simp)
      have hm : u∈sortedSupport31 f := by rw [hL]; simp
      have hu' := ((member_sortedSupport31 f u).mp hm).1
      have hT := (List.pairwise_cons.mp hTail).2
      refine ⟨⟨u,hu'⟩,hu,?_⟩
      apply normalizedList31_complete
      · exact (hT.imp (fun h=>le_of_lt h)).sortedLE
      · exact hT.imp (fun h=>ne_of_lt h)
      · simp only [List.length_cons] at hLen
        omega
      · intro x hx
        have hh : x∈sortedSupport31 f := by rw [hL]; simp [hx]
        exact ⟨(List.pairwise_cons.mp hTail).1 x hx,
          ((member_sortedSupport31 f x).mp hh).1⟩

/-- Explicit finite interface for *one actual physical support*.
When its degree-k coverage cells are certified, it is equal setwise to
one literal prototype after an independently verified translation/sign. -/
theorem actual_normalized_support_in_catalog31 (P : List (List Nat)) (k : Nat)
    (hCert : ∀ u : Fin 31, 0<u.val → coverage31At P k u.val=true)
    (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1) (hk2 : 2≤k)
    (hk : (∑z,f z)=(k:ℤ)) (h0 : f 0=1)
    (hNative : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1)
    (hAdj : cycleAuto31 f 1=0) :
    ∃ T∈P, ∃ e : Bool, ∃ t<31, ∀ a : Nat,
      (a<31 ∧ f (a:Z31)=1) ↔ a∈translateReflect31 T e t := by
  obtain ⟨u,hu,hS⟩ := normalization_input31 f hf k hk2 hk h0
  have hSort : (sortedSupport31 f).Pairwise (·<·) := (Finset.sortedLT_sort ((support31 f).image ZMod.val)).pairwise
  have hV := natural_support_passes_local31 f (sortedSupport31 f) hf hNative hAdj hSort
    (fun a ha => (member_sortedSupport31 f a).mp ha)
  obtain ⟨T,hT,e,t,ht,h⟩ := local_coverage31_sound (hCert u hu) hS hV
  exact ⟨T,hT,e,t,ht,fun a => (member_sortedSupport31 f a).symm.trans (h a)⟩

end Symconf93

#print axioms Symconf93.normalization_input31
#print axioms Symconf93.actual_normalized_support_in_catalog31
