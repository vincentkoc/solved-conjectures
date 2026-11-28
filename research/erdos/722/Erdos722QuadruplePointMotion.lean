import Erdos722SwitchIsomorphismLaw
import Erdos722SignedSteinerObstruction

/-! # A nonidentity automorphism of a Steiner quadruple system moves at least half its points -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
variable {n : ℕ} {H : Finset (Finset (Fin n))}

theorem pair_degree (hH : H.IsBlockDesign 3 4) {x a : Fin n} (hxa : x≠a) :
    2*(H.filter ({x,a}⊆·)).card=n-2 := by
  have hc : ({x,a} : Finset _).card=2 := by simp [hxa]
  have deg := IntegralDesign.flag_count hH {x,a} (by omega)
  simpa [hc] using deg

theorem moved_point_exists (σ : Perm (Fin n)) (hn : σ≠Equiv.refl _) : ∃ x, σ x≠x := by
  by_contra! h
  exact hn (Equiv.ext h)

/-- With a fixed point a and a moved point x, each block through a,x contains
at most one further fixed point. Three fixed points would force its fourth point to be fixed. -/
theorem point_motion (hH : H.IsBlockDesign 3 4) (σ : Perm (Fin n))
    (hp : σ.finsetCongr.finsetCongr H=H) (hn : σ≠Equiv.refl _) : n≤2*σ.support.card := by
  classical
  obtain ⟨x,hx⟩ := moved_point_exists σ hn
  let F := σ.supportᶜ
  have fixed (b : Fin n) : b∈F ↔ σ b=b := by simp [F,Perm.mem_support]
  have count : F.card=n-σ.support.card := by rw [show F=σ.supportᶜ from rfl,card_compl,Fintype.card_fin]
  have cap : σ.support.card≤n := by simpa using card_le_univ σ.support
  rcases F.eq_empty_or_nonempty with empty | ⟨a,ha⟩
  · rw [empty,card_empty] at count; omega
  have xa : x≠a := by rintro rfl; exact hx ((fixed x).mp ha)
  let J : Finset (Fin n) := {x,a}
  have Jcard : J.card=2 := by simp [J,xa]
  let L := F.erase a
  have memL (j : L) : j.val≠a ∧ σ j.val=j.val :=
    ⟨(mem_erase.mp j.prop).1,(fixed _).mp (mem_erase.mp j.prop).2⟩
  have newPt (j : L) : j.val∉J := by
    have nx : j.val≠x := fun eq => hx (eq ▸ (memL j).2)
    simp [J,nx,(memL j).1]
  choose B hB using fun j : L => (hH.2 (insert j.val J)
    (by rw [card_insert_of_notMem (newPt j),Jcard])).exists
  let P := H.filter (J⊆·)
  have inP (j : L) : B j∈P := mem_filter.mpr ⟨(hB j).1,(subset_insert ..).trans (hB j).2⟩
  have inj : Injective B := by
    intro i j eq
    by_contra ne
    have ij : i.val≠j.val := fun hv => ne (Subtype.ext hv)
    let T : Finset (Fin n) := {i.val,j.val,a}
    have tcard : T.card=3 := by simp [T,ij,(memL i).1,(memL j).1]
    have jt : j.val∈B i := eq ▸ (hB j).2 (mem_insert_self ..)
    have atB : a∈B i := (mem_filter.mp (inP i)).2 (by simp [J])
    have it : i.val∈B i := (hB i).2 (mem_insert_self ..)
    have sub : T⊆B i := insert_subset it (insert_subset jt (singleton_subset_iff.mpr atB))
    have pfix (z : Fin n) (hz : z∈T) : σ z=z := by
      simp only [T,mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact (memL i).2
      · exact (memL j).2
      · exact (fixed _).mp ha
    have sb : T⊆σ.finsetCongr (B i) := fun z hz =>
      pfix z hz ▸ mem_map.mpr ⟨z,sub hz,rfl⟩
    have beq := (hH.2 T tcard).unique ⟨hp ▸ mem_map.mpr ⟨B i,(hB i).1,rfl⟩,sb⟩ ⟨(hB i).1,sub⟩
    have xin : x∈B i := (mem_filter.mp (inP i)).2 (by simp [J])
    have sxin : σ x∈B i := beq ▸ mem_map.mpr ⟨x,xin,rfl⟩
    have xout : x∉T := fun hxT => hx (pfix _ hxT)
    have sxout : σ x∉T := fun hsT => hx (σ.injective (pfix _ hsT))
    have five : (insert (σ x) (insert x T)).card=5 := by simp [hx,sxout,xout,tcard]
    have le := card_le_card (insert_subset sxin (insert_subset xin sub))
    rw [five,hH.1 _ (hB i).1] at le
    omega
  have le := Fintype.card_le_of_injective (fun j : L => (⟨B j,inP j⟩ : P))
    (fun i j h => inj (congrArg Subtype.val h))
  rw [Fintype.card_coe,Fintype.card_coe,show L=F.erase a from rfl,card_erase_of_mem ha] at le
  have deg := pair_degree hH xa
  change 2*P.card=n-2 at deg
  have two := card_le_univ J
  rw [Jcard,Fintype.card_fin] at two
  omega

#print axioms pair_degree
#print axioms moved_point_exists
#print axioms point_motion
end Erdos722.QuadSwitch
