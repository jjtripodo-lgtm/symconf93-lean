module
public import Symconf59.Incidence
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

/-! Actual cycle coordinates for each connected component of any
finite simple degree-two graph, including either original leave. -/
namespace Symconf59

def cnext {n : ℕ} (i : Fin n) : Fin n :=
  letI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  i+1

def cprev {n : ℕ} (i : Fin n) : Fin n :=
  letI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  i-1

structure CycleLayout {V : Type*} (G : SimpleGraph V) where
  len : G.ConnectedComponent → ℕ
  minLen : ∀ c, 3≤len c
  sites : ∀ c, Fin (len c) ≃ c.supp
  adj : ∀ c (i j : Fin (len c)),
    G.Adj (sites c i).val (sites c j).val ↔ j=cnext i ∨ j=cprev i

section Graph
open SimpleGraph
variable {V : Type*} [Finite V] (G : SimpleGraph V)

theorem cnext_prev {n : ℕ} (i : Fin n) : cnext (cprev i)=i := by
  haveI : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  change (i-1)+1=i
  exact sub_add_cancel i 1

theorem next_prev_distinct {n : ℕ} (hn : 3≤n) (i : Fin n) :
    cnext i≠cprev i := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  change i+1=i-1 at h
  have h' : i+1+1=i := by rw [h,sub_add_cancel]
  have h₂ : (2:Fin n)=0 := by
    apply add_left_cancel (a:=i)
    have he : (1:Fin n)+1=2 := by
      apply Fin.ext
      change (1%n+1%n)%n=2%n
      rw [Nat.mod_eq_of_lt (by omega : 1<n)]
    rw [← he,← add_assoc,h',add_zero]
  have he := congrArg Fin.val h₂
  change (2%n)=0%n at he
  rw [Nat.mod_eq_of_lt (by omega : 2<n),Nat.zero_mod] at he
  omega

theorem component_chart_exists
    (hG : G.IsCycles) (hNonempty : ∀v, (G.neighborSet v).Nonempty)
    (c : G.ConnectedComponent) :
    ∃ (l : ℕ) (e : Fin l ≃ c.supp),
      3≤l ∧ ∀ i j, G.Adj (e i).val (e j).val ↔ j=cnext i ∨ j=cprev i := by
  classical
  obtain ⟨v,hv⟩ := c.nonempty_supp
  obtain ⟨w,hw,hV⟩ := hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv (hNonempty v)
  let l := w.length
  have hl : 3≤l := hw.three_le_length
  letI : NeZero l := ⟨by omega⟩
  let E : Fin l → c.supp := fun i => ⟨w.getVert i.val,by
    rw [← hV,Walk.mem_verts_toSubgraph]
    exact w.getVert_mem_support i.val⟩
  have hinj : Function.Injective E := by
    intro i j h
    apply Fin.ext
    exact hw.getVert_injOn' (by change i.val≤w.length-1; omega)
      (by change j.val≤w.length-1; omega) (congrArg Subtype.val h)
  have hsurj : Function.Surjective E := by
    intro z
    have hz : z.val∈w.support := by
      rw [← Walk.mem_verts_toSubgraph,hV]
      exact z.property
    obtain ⟨i,hi⟩ := List.get_of_mem hz
    have hie : w.getVert i.val=z.val := (w.support_getElem_eq_getVert i.isLt).symm.trans hi
    have hib : i.val≤l := by
      let j := i.val
      have hh : j<w.support.length := i.isLt
      rw [w.length_support] at hh
      change j≤l
      omega
    by_cases he : i.val=l
    · refine ⟨0,Subtype.ext ?_⟩
      change w.getVert 0=z.val
      rw [he,Walk.getVert_length] at hie
      rwa [Walk.getVert_zero]
    · refine ⟨⟨i.val,by omega⟩,Subtype.ext hie⟩
  let e := Equiv.ofBijective E ⟨hinj,hsurj⟩
  have hforward (i : Fin l) : G.Adj (e i).val (e (cnext i)).val := by
    have hh := w.adj_getVert_succ i.isLt
    change G.Adj (w.getVert i.val) (w.getVert (cnext i).val)
    have hs : (cnext i).val=(i.val+1)%l := by
      change (i.val+1%l)%l=(i.val+1)%l
      rw [Nat.mod_eq_of_lt (by omega : 1<l)]
    rw [hs]
    by_cases hi : i.val+1<l
    · simpa only [Nat.mod_eq_of_lt hi] using hh
    · have hv : i.val+1=l := by omega
      rw [hv,Nat.mod_self,Walk.getVert_zero]
      rw [hv,Walk.getVert_length] at hh
      exact hh
  have hback (i : Fin l) : G.Adj (e i).val (e (cprev i)).val := by
    have hh := (hforward (cprev i)).symm
    rwa [cnext_prev] at hh
  refine ⟨l,e,hl,?_⟩
  intro i j
  constructor
  · intro h
    by_cases he : j=cnext i
    · exact Or.inl he
    · right
      obtain ⟨a,ha,hUnique⟩ := hG.existsUnique_ne_adj (hforward i)
      have hn (j : Fin l) (h : j≠cnext i) : (e (cnext i)).val≠(e j).val :=
        fun heq => h (e.injective (Subtype.ext heq.symm))
      have ht := hUnique (e j).val ⟨hn j he,h⟩
      have hu := hUnique (e (cprev i)).val ⟨hn _ (next_prev_distinct hl i).symm,hback i⟩
      exact e.injective (Subtype.ext (ht.trans hu.symm))
  · rintro (rfl|rfl)
    · exact hforward i
    · exact hback i

/-- No spectral theorem: choose genuine simple cycle coordinates component
by component using the pin's exact finite-walk lemma. -/
noncomputable def cycleLayout_of_two_regular
    (hG : G.IsCycles) (hNonempty : ∀v, (G.neighborSet v).Nonempty) : CycleLayout G := by
  classical
  have hs := component_chart_exists G hG hNonempty
  choose l e hmin hadj using hs
  exact ⟨l,hmin,e,hadj⟩

end Graph

end Symconf59

namespace Symconf59
open SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

/-- The actual graph vertices are exhausted once by its disjoint
component supports. -/
noncomputable def graphComponentSites : (Σ c : G.ConnectedComponent, c.supp) ≃ V := by
  let f : (Σ c : G.ConnectedComponent, c.supp) → V := fun p => p.2.val
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨c,x⟩ ⟨d,y⟩ h
    change x.val=y.val at h
    have hc := (ConnectedComponent.mem_supp_iff c x.val).mp x.property
    have hd := (ConnectedComponent.mem_supp_iff d y.val).mp y.property
    have he : c=d := by
      rw [h] at hc
      exact hc.symm.trans hd
    subst d
    have hxy : x=y := Subtype.ext h
    subst y
    rfl
  · intro v
    exact ⟨⟨G.connectedComponentMk v,⟨v,(ConnectedComponent.mem_supp_iff _ _).mpr rfl⟩⟩,rfl⟩

/-- A global coordinate chart for every literal site in the leave,
not a separate comparison of isolated cycle counts. -/
noncomputable def CycleLayout.allSites {G : SimpleGraph V} (L : CycleLayout G) :
    (Σ c : G.ConnectedComponent, Fin (L.len c)) ≃ V :=
  (Equiv.sigmaCongrRight L.sites).trans (graphComponentSites G)

theorem CycleLayout.total_length {G : SimpleGraph V} [Fintype V] [Fintype G.ConnectedComponent]
    (L : CycleLayout G) : (∑ c, L.len c)=Fintype.card V := by
  have h := Fintype.card_congr L.allSites
  simpa only [Fintype.card_sigma,Fintype.card_fin] using h

theorem CycleLayout.disjoint_component_adj {G : SimpleGraph V} (L : CycleLayout G)
    {c d : G.ConnectedComponent} (h : c≠d) (i : Fin (L.len c)) (j : Fin (L.len d)) :
    ¬G.Adj (L.sites c i).val (L.sites d j).val := by
  intro hA
  have hp := c.mem_supp_of_adj_mem_supp (L.sites c i).property hA
  have hc := (ConnectedComponent.mem_supp_iff c _).mp hp
  have hd := (ConnectedComponent.mem_supp_iff d _).mp (L.sites d j).property
  exact h (hc.symm.trans hd)

open Matrix

def leaveGraph (M : Int59) (hdiag : ∀i,M i i=0) (hs : Mᵀ=M) : SimpleGraph Site where
  Adj i j := M i j=1
  symm := ⟨by
    intro i j h
    have he := congrArg (fun (B : Int59) => B i j) hs
    exact he.trans h⟩
  loopless := ⟨by
    intro i h
    change M i i=1 at h
    rw [hdiag] at h
    contradiction⟩

private theorem int_count_ones (f : Site → ℤ) (h : ∀ i, f i=0 ∨ f i=1) :
    (∑ i,f i)=((Finset.univ.filter (fun i=>f i=1)).card:ℤ) := by
  have h' (i : Site) : f i=(if f i=1 then 1 else 0 : ℤ) := by
    rcases h i with h | h <;> simp [h]
  calc
    _ = ∑ i, (if f i=1 then 1 else 0 : ℤ) := Finset.sum_congr rfl (fun i _ => h' i)
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem binary_leave_graph_two_regular (M : Int59)
    (hdiag : ∀i,M i i=0) (hs : Mᵀ=M) (hb : ∀i j,M i j=0 ∨ M i j=1)
    (hm : ∀i,(∑ j,M i j)=2) :
    ∀ i, ((leaveGraph M hdiag hs).neighborSet i).ncard=2 := by
  intro i
  let S := (leaveGraph M hdiag hs).neighborSet i
  have he : S.toFinite.toFinset=Finset.univ.filter (fun j => M i j=1) := by
    ext j
    simp [S,leaveGraph,SimpleGraph.mem_neighborSet]
  calc
    S.ncard = S.toFinite.toFinset.card := Set.ncard_eq_toFinset_card _ _
    _ = (Finset.univ.filter (fun j => M i j=1)).card := by rw [he]
    _ = 2 := by
      have h := int_count_ones (M i) (hb i)
      rw [hm] at h
      omega

theorem both_cycle_conditions (M : Int59)
    (hd : ∀i,M i i=0) (hs : Mᵀ=M) (hb : ∀ i j,M i j=0 ∨ M i j=1)
    (hR : ∀i,(∑j,M i j)=2) :
    (leaveGraph M hd hs).IsCycles ∧ ∀v, ((leaveGraph M hd hs).neighborSet v).Nonempty := by
  have hk := binary_leave_graph_two_regular M hd hs hb hR
  exact ⟨fun {_} _ => hk _,fun v => Set.nonempty_of_ncard_ne_zero (by rw [hk]; decide)⟩

/-- Actual one-by-one cyclic components of the original row leave, no
assumption on the number of components or the incidence automorphism. -/
noncomputable def originalRowLayout {A : Int59} (h : Incidence59 A) :
    CycleLayout (leaveGraph (rowLeave A) (rowLeave_diag h) (rowLeave_symm A)) := by
  have hc := both_cycle_conditions (rowLeave A) (rowLeave_diag h) (rowLeave_symm A)
    (rowLeave_binary h) (rowLeave_sum h)
  exact cycleLayout_of_two_regular _ hc.1 hc.2

end Symconf59
