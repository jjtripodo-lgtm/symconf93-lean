module
public import Symconf93.ActualBlockOrbit31
public import Symconf93.WitnessBucketsSound

@[expose] public section

/-! Exact original circle-block support classification at the small
degrees already covered by kernel-checked normalized support cells. -/
namespace Symconf93
open scoped BigOperators

theorem actual_degree2_orbit31 (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1)
    (h2 : (∑ z,f z)=2)
    (hNative : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1) (hAdj : cycleAuto31 f 1=0) :
    ∃ T∈proto2, ∃ e : Bool, ∃ a : Z31, ∀ z : Z31,
      f z=1 ↔ ∃ x∈supportReflect31 e T, z=(x:Z31)+a :=
  actual_block_signed_orbit31 proto2 2 local2_coverage_verified f hf
    (by decide) h2 hNative hAdj

theorem actual_degree3_orbit31 (f : Z31→ℤ) (hf : ∀ z,f z=0∨f z=1)
    (h3 : (∑ z,f z)=3)
    (hNative : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1) (hAdj : cycleAuto31 f 1=0) :
    ∃ T∈proto3, ∃ e : Bool, ∃ a : Z31, ∀ z : Z31,
      f z=1 ↔ ∃ x∈supportReflect31 e T, z=(x:Z31)+a :=
  actual_block_signed_orbit31 proto3 3 local3_coverage_verified f hf
    (by decide) h3 hNative hAdj

end Symconf93

#print axioms Symconf93.actual_degree2_orbit31
#print axioms Symconf93.actual_degree3_orbit31
