module
public import Symconf93.ActualSupportCatalog31
public import Symconf93.PhasePairsBase

@[expose] public section

namespace Symconf93
open scoped BigOperators

/-- Reading the setwise certified natural orbit as a true Z/31 translate
of the signed unshifted prototype. -/
private theorem natural_orbit_cast31 (T : List Nat) (e : Bool) (t : Nat) (z : Z31) :
    z.val∈translateReflect31 T e t ↔
      ∃ x∈supportReflect31 e T, z=(x:Z31)+(t:Z31) := by
  have sum_cast (x : Nat) : (((t+x)%31:Nat):Z31)=(t:Z31)+(x:Z31) := by
    rw [ZMod.natCast_mod,Nat.cast_add]
  have eq_val {x : Nat} (h : z=(t:Z31)+(x:Z31)) : z.val=(t+x)%31 := by
    rw [←sum_cast] at h
    simpa only [ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0<31))] using
      congrArg ZMod.val h
  cases e
  · constructor
    · intro hh
      obtain ⟨a,ha,hv⟩ := List.mem_map.mp hh
      have he : (t+a)%31=z.val := hv
      refine ⟨a,ha,?_⟩
      rw [add_comm]
      exact (ZMod.natCast_zmod_val z).symm.trans
        ((congrArg (fun x : Nat => (x:Z31)) he).symm.trans (sum_cast a))
    · rintro ⟨a,ha,hz⟩
      apply List.mem_map.mpr
      exact ⟨a,ha,(eq_val (by rwa [add_comm] at hz)).symm⟩
  · constructor
    · intro hh
      obtain ⟨a,ha,hv⟩ := List.mem_map.mp hh
      have he : (t+(31-a))%31=z.val := hv
      refine ⟨(31-a)%31,List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
      rw [ZMod.natCast_mod,add_comm]
      exact (ZMod.natCast_zmod_val z).symm.trans
        ((congrArg (fun x : Nat => (x:Z31)) he).symm.trans (sum_cast (31-a)))
    · rintro ⟨a,ha,hz⟩
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      rw [ZMod.natCast_mod,add_comm] at hz
      exact List.mem_map.mpr ⟨v,hv,(eq_val hz).symm⟩

/-- Any actual block that passes the original autocorrelation bounds, if
the exact degree catalog has been checked, is a true signed prototype
translate. The claimed equivalence is on every actual residue, not on
indices under an unproved sort/phase correspondence. -/
theorem actual_block_signed_orbit31 (P : List (List Nat)) (k : Nat)
    (hCert : ∀ u : Fin 31, 0<u.val → coverage31At P k u.val=true)
    (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1) (hk2 : 2≤k)
    (hk : (∑z,f z)=(k:ℤ))
    (hNative : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1)
    (hAdj : cycleAuto31 f 1=0) :
    ∃ T∈P, ∃ e : Bool, ∃ a : Z31, ∀ z : Z31,
      f z=1 ↔ ∃ x∈supportReflect31 e T, z=(x:Z31)+a := by
  have hp : 0<∑z,f z := by rw [hk]; exact_mod_cast (by omega : 0<k)
  obtain ⟨w,hw,hAuto⟩ := normalize_one_support31 f hf hp
  let g := translatedSupport31 f w
  have hg : ∀ z,g z=0∨g z=1 := fun z => hf (z-w)
  have hgS : (∑z,g z)=(k:ℤ) := by
    have hh := Equiv.sum_comp (Equiv.addRight (-w)) f
    change (∑z,f (z+(-w)))=∑z,f z at hh
    change (∑z,f (z-w))=(k:ℤ)
    simpa only [sub_eq_add_neg] using hh.trans hk
  have hgN : ∀ d : Z31,d≠0 → cycleAuto31 g d≤1 := by
    intro d hd
    change cycleAuto31 (translatedSupport31 f w) d≤1
    rw [hAuto]
    exact hNative d hd
  have hgA : cycleAuto31 g 1=0 := (hAuto 1).trans hAdj
  obtain ⟨T,hT,e,t,ht,hT'⟩ :=
    actual_normalized_support_in_catalog31 P k hCert g hg hk2 hgS hw hgN hgA
  refine ⟨T,hT,e,(t:Z31)-w,fun z => ?_⟩
  have hv : g (((z+w).val:Nat):Z31)=f z := by
    rw [ZMod.natCast_zmod_val]
    change f (z+w-w)=f z
    rw [add_sub_cancel_right]
  have he := hT' (z+w).val
  rw [hv] at he
  have hc : f z=1 ↔ (z+w).val∈translateReflect31 T e t := by
    rw [←he]
    exact ⟨fun h=>⟨ZMod.val_lt _,h⟩,fun h=>h.2⟩
  rw [hc,natural_orbit_cast31]
  constructor <;> rintro ⟨x,hx,h⟩ <;> refine ⟨x,hx,?_⟩ <;>
    linear_combination h

end Symconf93

#print axioms Symconf93.actual_block_signed_orbit31
