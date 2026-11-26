module
public import Symconf93.Support31Physical
public import Symconf93.LocalCatalogBase
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! The physical gap partition forces any sorted list of actual support
points to pass the exact normalized-catalogue gap test. -/
namespace Symconf93
open scoped BigOperators

def nativeGap31 (a b : Nat) : Nat := min (b-a) (31-(b-a))

private theorem gap31_bounds {a b : Nat} (hab : a<b) (hb : b<31) :
    0<nativeGap31 a b ∧ nativeGap31 a b≤15 := by
  unfold nativeGap31
  omega

private theorem gap31_as_residue {f : Z31→ℤ} {a b : Nat}
    (hab : a<b) (hb : b<31) (ha : f (a:Z31)=1) (hf : f (b:Z31)=1) :
    ∃ p : Z31×Z31, p∈residuePairs31 f f (nativeGap31 a b) ∧
      (p=((a:Z31),(b:Z31)) ∨ p=((b:Z31),(a:Z31))) := by
  have hcast : ((b-a:Nat):Z31)=(b:Z31)-(a:Z31) := Nat.cast_sub (by omega)
  have hz : ((31:Nat):Z31)=0 := ZMod.natCast_self 31
  by_cases h : b-a≤31-(b-a)
  · refine ⟨((a:Z31),(b:Z31)),?_,Or.inl rfl⟩
    simp [residuePairs31,support31,ha,hf,nativeGap31,min_eq_left h,hcast]
  · have h' : 31-(b-a)≤b-a := by omega
    have hh : ((31-(b-a):Nat):Z31)=(a:Z31)-(b:Z31) := by
      rw [Nat.cast_sub (by omega),hcast,hz,zero_sub]
      ring
    refine ⟨((b:Z31),(a:Z31)),?_,Or.inr rfl⟩
    simp [residuePairs31,support31,ha,hf,nativeGap31,min_eq_right h',hh]

private theorem valid_support_gap31
    {f : Z31→ℤ} (hf : ∀ z, f z=0 ∨ f z=1)
    (h1 : cycleAuto31 f 1=0)
    {a b : Nat} (hab : a<b) (hb : b<31)
    (ha : f (a:Z31)=1) (hB : f (b:Z31)=1) :
    2≤nativeGap31 a b ∧ nativeGap31 a b≤15 := by
  have hh := gap31_bounds hab hb
  refine ⟨?_,hh.2⟩
  by_contra! hn
  have he : nativeGap31 a b=1 := by omega
  obtain ⟨p,hp,_⟩ := gap31_as_residue hab hb ha hB
  rw [he] at hp
  change cycleCorr31 f f 1=0 at h1
  rw [cycleCorr31_literal_pairs hf hf] at h1
  have hp' : 0<(residuePairs31 f f (1:Z31)).card := Finset.card_pos.mpr ⟨p,hp⟩
  omega

private theorem unique_support_gap31
    {f : Z31→ℤ} (hf : ∀ z,f z=0∨f z=1)
    (h1 : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1)
    {a b c d : Nat} (hab : a<b) (hcd : c<d)
    (hb : b<31) (hd : d<31)
    (ha : f (a:Z31)=1) (hB : f (b:Z31)=1)
    (hC : f (c:Z31)=1) (hD : f (d:Z31)=1)
    (he : nativeGap31 a b=nativeGap31 c d) : (a,b)=(c,d) := by
  have hbound := gap31_bounds hab hb
  have hn : (nativeGap31 a b:Z31)≠0 := by
    intro hh
    have h := congrArg ZMod.val hh
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at h
    omega
  have hsmall := h1 (nativeGap31 a b) hn
  change cycleCorr31 f f (nativeGap31 a b)≤1 at hsmall
  rw [cycleCorr31_literal_pairs hf hf] at hsmall
  obtain ⟨p,hp,pdef⟩ := gap31_as_residue hab hb ha hB
  obtain ⟨q,hq,qdef⟩ := gap31_as_residue hcd hd hC hD
  rw [←he] at hq
  have hc : (residuePairs31 f f (nativeGap31 a b)).card≤1 := by exact_mod_cast hsmall
  have hpq := Finset.card_le_one.mp hc p hp q hq
  have eqCast {x y:Nat} (hx : x<31) (hy : y<31) (h : (x:Z31)=(y:Z31)) : x=y := by
    have hz := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hx,ZMod.val_natCast_of_lt hy] using hz
  rcases pdef with rfl|rfl <;> rcases qdef with rfl|rfl
  · exact Prod.ext (eqCast (by omega) (by omega) (congrArg Prod.fst hpq))
      (eqCast hb hd (congrArg Prod.snd hpq))
  · have hA := eqCast (by omega) hd (congrArg Prod.fst hpq)
    have hB := eqCast hb (by omega : c<31) (congrArg Prod.snd hpq)
    omega
  · have hA := eqCast hb (by omega : c<31) (congrArg Prod.fst hpq)
    have hB := eqCast (by omega : a<31) hd (congrArg Prod.snd hpq)
    omega
  · exact Prod.ext (eqCast (by omega) (by omega) (congrArg Prod.snd hpq))
      (eqCast hb hd (congrArg Prod.fst hpq))

def naturalPairs31 : List Nat→List (Nat×Nat)
  | [] => []
  | a::L => (L.map fun b => (a,b)) ++ naturalPairs31 L

private theorem mem_naturalPairs31 (L : List Nat) (hL : L.Pairwise (·<·)) :
    ∀ p∈naturalPairs31 L, p.1∈L ∧ p.2∈L ∧ p.1<p.2 := by
  induction L with
  | nil => simp [naturalPairs31]
  | cons a T ih =>
    intro p hp
    simp only [naturalPairs31,List.mem_append,List.mem_map] at hp
    rcases hp with ⟨b,hb,rfl⟩|hp
    · exact ⟨by simp,List.mem_cons_of_mem _ hb,(List.pairwise_cons.mp hL).1 b hb⟩
    · obtain ⟨h1,h2,h3⟩ := ih (List.pairwise_cons.mp hL).2 p hp
      exact ⟨List.mem_cons_of_mem _ h1,List.mem_cons_of_mem _ h2,h3⟩

private theorem naturalPairs31_nodup (L : List Nat) (hL : L.Pairwise (·<·)) :
    (naturalPairs31 L).Nodup := by
  induction L with
  | nil => simp [naturalPairs31]
  | cons a T ih =>
    have ht := (List.pairwise_cons.mp hL).2
    simp only [naturalPairs31,List.nodup_append]
    refine ⟨?_,ih ht,?_⟩
    · apply List.Nodup.map
      · intro x y h
        exact congrArg Prod.snd h
      · exact ht.imp (fun h => ne_of_lt h)
    · intro p h1 q h2 he
      subst q
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h1
      have hA := (mem_naturalPairs31 T ht _ h2).1
      exact (lt_irrefl a) ((List.pairwise_cons.mp hL).1 _ hA)

private theorem gap_list_identity (L : List Nat) :
    unsignedGaps31 L = (naturalPairs31 L).map (fun p => nativeGap31 p.1 p.2) := by
  induction L with
  | nil => rfl
  | cons a T ih =>
    simp only [unsignedGaps31,naturalPairs31,List.map_append,List.map_map,
      ih,nativeGap31]
    rfl

/-- Sound actual support → finite local normalizer input, no assumptions
on relative shifts or reflection choice. -/
theorem natural_support_passes_local31 (f : Z31→ℤ) (L : List Nat)
    (hf : ∀ z,f z=0∨f z=1)
    (hAuto : ∀ d : Z31,d≠0 → cycleAuto31 f d≤1)
    (hAdj : cycleAuto31 f 1=0)
    (hL : L.Pairwise (·<·))
    (hP : ∀ a∈L,a<31 ∧ f (a:Z31)=1) :
    validLocal31 L=true := by
  unfold validLocal31
  rw [gap_list_identity,Bool.and_eq_true]
  constructor
  · apply decide_eq_true
    rw [List.nodup_map_iff_inj_on (naturalPairs31_nodup L hL)]
    intro p hp q hq heq
    obtain ⟨hp1,hp2,hpl⟩ := mem_naturalPairs31 L hL p hp
    obtain ⟨hq1,hq2,hql⟩ := mem_naturalPairs31 L hL q hq
    exact unique_support_gap31 hf hAuto hpl hql (hP _ hp2).1 (hP _ hq2).1
      (hP _ hp1).2 (hP _ hp2).2 (hP _ hq1).2 (hP _ hq2).2 heq
  · apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    obtain ⟨h1,h2,h3⟩ := mem_naturalPairs31 L hL p hp
    exact decide_eq_true (valid_support_gap31 hf hAdj h3 (hP _ h2).1 (hP _ h1).2 (hP _ h2).2)

end Symconf93

#print axioms Symconf93.natural_support_passes_local31
