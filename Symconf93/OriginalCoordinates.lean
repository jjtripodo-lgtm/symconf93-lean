module
public import Symconf93.CycleOrientation
public import Symconf59.CyclicBlock
public import Symconf59.OrderedLengths
public import Symconf93.PhysicalBlockProfile

@[expose] public section

/-! The two actual graph layouts on a single ordered original profile,
and every induced block invariant on the actual incidence entries. -/
namespace Symconf93
open Symconf59
open Matrix SimpleGraph Fin.NatCast
open scoped BigOperators Matrix

private theorem finCongr_next {a b : ℕ} (h : a=b) (i : Fin a) :
    finCongr h (cnext i)=cnext (finCongr h i) := by subst b; rfl
private theorem finCongr_prev {a b : ℕ} (h : a=b) (i : Fin a) :
    finCongr h (cprev i)=cprev (finCongr h i) := by subst b; rfl

structure OrderedCycles (M : Int93) (P : List ℕ) where
  sites : BlocksOf P ≃ Site
  orientation : Equiv.Perm Site
  trueMatrix : M=symmetricStep orientation 1
  forward : ∀ i (x : Fin (P.get i)), orientation (sites ⟨i,x⟩)=sites ⟨i,cnext x⟩
  backward : ∀ i (x : Fin (P.get i)), orientation⁻¹ (sites ⟨i,x⟩)=sites ⟨i,cprev x⟩

private noncomputable def order_cycle_sites {M : Int93} {P : List ℕ}
    (hd : ∀ i,M i i=0) (hs : Mᵀ=M) (hb : ∀ i j,M i j=0 ∨ M i j=1)
    (L : CycleLayout (leaveGraph M hd hs))
    (e : Fin P.length ≃ (leaveGraph M hd hs).ConnectedComponent)
    (he : ∀ i,P.get i=L.len (e i)) : OrderedCycles M P := by
  let E := (Equiv.sigmaCongr e (fun i => finCongr (he i))).trans L.allSites
  refine ⟨E,L.rotation,leave_matrix_from_rotation M hd hs hb L,?_,?_⟩
  · intro i x
    change L.rotation (L.allSites ⟨e i,finCongr (he i) x⟩)=_
    rw [L.rotation_forward]
    exact congrArg (fun y => L.allSites ⟨e i,y⟩) (finCongr_next (he i) x).symm
  · intro i x
    change L.rotation⁻¹ (L.allSites ⟨e i,finCongr (he i) x⟩)=_
    rw [L.rotation_backward]
    exact congrArg (fun y => L.allSites ⟨e i,y⟩) (finCongr_prev (he i) x).symm

theorem OrderedCycles.same_block {M : Int93} {P : List ℕ} (C : OrderedCycles M P)
    (i : Fin P.length) (x y : Fin (P.get i)) :
    M (C.sites ⟨i,x⟩) (C.sites ⟨i,y⟩)=
      (if y=cnext x then 1 else 0)+(if y=cprev x then 1 else 0) := by
  have h (b : Fin (P.get i)) : C.sites ⟨i,y⟩=C.sites ⟨i,b⟩ ↔ y=b := by
    constructor
    · exact fun he => eq_of_heq (Sigma.mk.inj_iff.mp (C.sites.injective he)).2
    · exact fun he => congrArg (fun z => C.sites ⟨i,z⟩) he
  refine (congrArg (fun M' : Int93 => M' (C.sites ⟨i,x⟩) (C.sites ⟨i,y⟩))
    C.trueMatrix).trans ?_
  simp only [symmetricStep,pow_one,Matrix.add_apply,permMat,C.forward,C.backward,h]

theorem OrderedCycles.different_blocks {M : Int93} {P : List ℕ} (C : OrderedCycles M P)
    {i j : Fin P.length} (hij : i≠j) (x : Fin (P.get i)) (y : Fin (P.get j)) :
    M (C.sites ⟨i,x⟩) (C.sites ⟨j,y⟩)=0 := by
  have hf (b : Fin (P.get i)) : C.sites ⟨j,y⟩≠C.sites ⟨i,b⟩ := by
    intro h
    exact hij ((Sigma.mk.inj_iff.mp (C.sites.injective h)).1.symm)
  refine (congrArg (fun M' : Int93 => M' (C.sites ⟨i,x⟩) (C.sites ⟨j,y⟩))
    C.trueMatrix).trans ?_
  simp only [symmetricStep,pow_one,Matrix.add_apply,permMat,C.forward,C.backward,if_neg (hf _),add_zero]

theorem OrderedCycles.same_block_sum {M : Int93} {P : List ℕ} (C : OrderedCycles M P)
    (i : Fin P.length) (x : Fin (P.get i)) :
    (∑ y : Fin (P.get i),M (C.sites ⟨i,x⟩) (C.sites ⟨i,y⟩))=2 := by
  simp [C.same_block,Finset.sum_add_distrib,Finset.sum_ite_eq']

/-- Put both actual row and column leaves in one decreasing profile. -/
theorem original_ordered_cycle_coords {A : Int93} (hA : Incidence93 A) :
    ∃ P : List ℕ, P.sum=93 ∧ (∀ a∈P,3≤a) ∧ P.Pairwise (· ≥ ·) ∧
      Nonempty (OrderedCycles (rowLeave A) P) ∧ Nonempty (OrderedCycles (colLeave A) P) := by
  classical
  obtain ⟨e,he⟩ := original_match_cycle_components hA
  let L := originalRowLayout hA
  let R := originalRowLayout hA.transpose
  letI : Fintype (leaveGraph (rowLeave A) (rowLeave_diag hA) (rowLeave_symm A)).ConnectedComponent :=
    Fintype.ofFinite _
  let O := order_actual_lengths L.len
  refine ⟨O.values,?_,?_,O.sorted,?_,?_⟩
  · have hT := O.sum_values.trans L.total_length
    simpa only [Fintype.card_fin] using hT
  · intro a ha
    obtain ⟨i,hi⟩ := List.get_of_mem ha
    rw [← hi,O.size_eq]
    exact L.minLen (O.label i)
  · exact ⟨order_cycle_sites _ _ (rowLeave_binary hA) L O.label O.size_eq⟩
  · exact ⟨order_cycle_sites _ _ (rowLeave_binary hA.transpose) R (O.label.trans e)
      (fun i => (O.size_eq i).trans (he (O.label i)).symm)⟩

private theorem original_block_wave {A : Int93} (hA : Incidence93 A)
    {P : List ℕ} (R : OrderedCycles (rowLeave A) P) (C : OrderedCycles (colLeave A) P)
    (i j : Fin P.length) (x : Fin (P.get i)) (y : Fin (P.get j)) :
    A (R.sites ⟨i,cnext x⟩) (C.sites ⟨j,y⟩)+A (R.sites ⟨i,cprev x⟩) (C.sites ⟨j,y⟩)=
    A (R.sites ⟨i,x⟩) (C.sites ⟨j,cnext y⟩)+A (R.sites ⟨i,x⟩) (C.sites ⟨j,cprev y⟩) := by
  have h : symmetricStep R.orientation 1*A=A*symmetricStep C.orientation 1 := by
    rw [← R.trueMatrix,← C.trueMatrix]
    exact leave_intertwines hA
  have hh := congrArg (fun (M : Int93) => M (R.sites ⟨i,x⟩) (C.sites ⟨j,y⟩)) h
  simp only [symmetricStep,pow_one,add_mul,mul_add,Matrix.add_apply,permMat_left,permMat_right,
    inv_inv,R.forward,R.backward,C.forward,C.backward] at hh
  exact hh.trans (add_comm _ _)

section Normalization
variable {P : List ℕ} {A : Int93}
variable (R : OrderedCycles (rowLeave A) P) (C : OrderedCycles (colLeave A) P)
variable (i j : Fin P.length) [NeZero (P.get i)] [NeZero (P.get j)]

def zblock (x : ZMod (P.get i)) (y : ZMod (P.get j)) : ℤ :=
  A (R.sites ⟨i,(ZMod.finEquiv _).symm x⟩) (C.sites ⟨j,(ZMod.finEquiv _).symm y⟩)

theorem zblock_wave (hA : Incidence93 A) : BlockWave (zblock R C i j) := by
  intro x y
  let ei := ZMod.finEquiv (P.get i)
  let ej := ZMod.finEquiv (P.get j)
  have en {n : ℕ} [NeZero n] (e : Fin n ≃+* ZMod n) (z : ZMod n) :
      e.symm (z+1)=cnext (e.symm z) := by
    change e.symm (z+1)=e.symm z+1
    rw [map_add,map_one]
  have ep {n : ℕ} [NeZero n] (e : Fin n ≃+* ZMod n) (z : ZMod n) :
      e.symm (z-1)=cprev (e.symm z) := by
    change e.symm (z-1)=e.symm z-1
    rw [map_sub,map_one]
  simp only [zblock,en,ep]
  exact original_block_wave hA R C i j (ei.symm x) (ej.symm y)

theorem row_count_constant (hA : Incidence93 A) (x : Fin (P.get i)) :
    (∑ y : Fin (P.get j), A (R.sites ⟨i,x⟩) (C.sites ⟨j,y⟩))=
      ∑ y : Fin (P.get j), A (R.sites ⟨i,0⟩) (C.sites ⟨j,y⟩) := by
  let ei := ZMod.finEquiv (P.get i)
  let ej := ZMod.finEquiv (P.get j)
  have h := cyclic_block_rows_constant _ (zblock_wave R C i j hA) (ei x)
  have ha (u : Fin (P.get i)) :
      (∑ y : ZMod (P.get j),zblock R C i j (ei u) y)=
      ∑ y : Fin (P.get j), A (R.sites ⟨i,u⟩) (C.sites ⟨j,y⟩) := by
    simp only [zblock,ei,RingEquiv.symm_apply_apply]
    exact Equiv.sum_comp ej.symm.toEquiv (fun y => A (R.sites ⟨i,u⟩) (C.sites ⟨j,y⟩))
  rw [ha] at h
  rw [← map_zero ei] at h
  rw [ha] at h
  exact h

theorem col_count_constant (hA : Incidence93 A) (y : Fin (P.get j)) :
    (∑ x : Fin (P.get i), A (R.sites ⟨i,x⟩) (C.sites ⟨j,y⟩))=
      ∑ x : Fin (P.get i), A (R.sites ⟨i,x⟩) (C.sites ⟨j,0⟩) := by
  let ei := ZMod.finEquiv (P.get i)
  let ej := ZMod.finEquiv (P.get j)
  have h := cyclic_block_cols_constant _ (zblock_wave R C i j hA) (ej y)
  have ha (v : Fin (P.get j)) :
      (∑ x : ZMod (P.get i),zblock R C i j x (ej v))=
      ∑ x : Fin (P.get i), A (R.sites ⟨i,x⟩) (C.sites ⟨j,v⟩) := by
    simp only [zblock,ej,RingEquiv.symm_apply_apply]
    exact Equiv.sum_comp ei.symm.toEquiv (fun x => A (R.sites ⟨i,x⟩) (C.sites ⟨j,v⟩))
  rw [ha] at h
  rw [← map_zero ej] at h
  rw [ha] at h
  exact h

private theorem zmod_fin_natCast (n d : ℕ) [NeZero n] :
    ZMod.finEquiv n (d:Fin n)=(d:ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

theorem exact_original_shift (hA : Incidence93 A) (d : ℕ) (hd : d<P.get i)
    (hG : Nat.gcd (P.get i) (P.get j)∣d) (y : Fin (P.get j)) :
    A (R.sites ⟨i,0⟩) (C.sites ⟨j,y⟩)=A (R.sites ⟨i,⟨d,hd⟩⟩) (C.sites ⟨j,y⟩) := by
  let ei := ZMod.finEquiv (P.get i)
  let ej := ZMod.finEquiv (P.get j)
  have hb : ∀ x y, zblock R C i j x y=0 ∨ zblock R C i j x y=1 := by
    intro x y
    exact hA.binary _ _
  have hf := cyclic_block_binary_gcd_period _ (zblock_wave R C i j hA) hb d hG 0 (ej y)
  have hz : ei (⟨d,hd⟩ : Fin (P.get i))=(d:ZMod (P.get i)) := by
    have hz' : (d:Fin (P.get i))=(⟨d,hd⟩ : Fin (P.get i)) := by
      apply Fin.ext
      change d % (P.get i)=d
      exact Nat.mod_eq_of_lt hd
    rw [← hz']
    exact zmod_fin_natCast _ _
  rw [zero_add,← hz,← map_zero ei] at hf
  simpa only [zblock,ei,ej,RingEquiv.symm_apply_apply] using hf.symm

end Normalization

theorem sum_nat_binary {n : ℕ} (g : Fin n → ℤ) (h : ∀ x, g x=0 ∨ g x=1) :
    ((∑ x,g x).toNat:ℤ)=∑ x,g x := by
  apply Int.toNat_of_nonneg
  apply Finset.sum_nonneg
  intro x _
  rcases h x with hx|hx <;> omega

/-- The original incidence matrix supplies all required charts, exact
block degrees, and actual distinct rows with each simultaneous period. -/
noncomputable def physical_of_ordered_cycles {A : Int93} (hA : Incidence93 A)
    {P : List ℕ} (hpos : ∀ a∈P,3≤a)
    (R : OrderedCycles (rowLeave A) P) (C : OrderedCycles (colLeave A) P) :
    PhysicalBlocks A P := by
  letI (i : Fin P.length) : NeZero (P.get i) :=
    ⟨by have := hpos _ (List.get_mem P i); omega⟩
  let u (i j : Fin P.length) := (∑ y : Fin (P.get j),A (R.sites ⟨i,0⟩) (C.sites ⟨j,y⟩)).toNat
  let v (i j : Fin P.length) := (∑ x : Fin (P.get i),A (R.sites ⟨i,x⟩) (C.sites ⟨j,0⟩)).toNat
  refine ⟨R.sites,C.sites,R.same_block_sum,fun i j h => R.different_blocks h,u,v,?_,?_,?_⟩
  · intro i j x
    rw [row_count_constant R C i j hA]
    exact (sum_nat_binary (fun y => A (R.sites ⟨i,0⟩) (C.sites ⟨j,y⟩)) (fun y => hA.binary _ _)).symm
  · intro i j y
    rw [col_count_constant R C i j hA]
    exact (sum_nat_binary (fun x => A (R.sites ⟨i,x⟩) (C.sites ⟨j,0⟩)) (fun x => hA.binary _ _)).symm
  · intro i d hd hd'
    refine ⟨0,⟨d,hd'⟩,?_,?_⟩
    · intro h
      have hh := congrArg Fin.val h
      change 0=d at hh
      omega
    · intro j hG y
      exact exact_original_shift R C i j hA d hd' hG y

end Symconf93
