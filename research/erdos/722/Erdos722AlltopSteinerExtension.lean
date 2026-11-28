import Erdos722AlltopWeightEquivalence
import Mathlib.Data.Finset.Option

/-! # Alltop's extension on ordinary labelled Steiner systems -/

namespace Erdos722.ComplementExtension
open Finset IntegralDesign Function
variable {α : Type*} [Fintype α] [DecidableEq α]

def punctured (α : Type*) [Fintype α] : Finset (Option α) := univ.map Embedding.some

omit [DecidableEq α] in
private theorem none_out : (none : Option α)∉punctured α := by simp [punctured]

private theorem add_point : insert (none : Option α) (punctured α)=univ := by
  ext i
  cases i <;> simp [punctured]

omit [DecidableEq α] in
private theorem punctured_card : (punctured α).card=Fintype.card α := by simp [punctured]

omit [Fintype α] in
private theorem incidence_map_some (V A : Finset α) (k : ℕ) (z : Finset (Option α) → ℤ) :
    incidence (V.map Embedding.some) k z (A.map Embedding.some)=
      incidence V k (fun B => z (B.map Embedding.some)) A := by
  simp only [incidence,sum_filter,powersetCard_map,sum_map]
  apply sum_congr rfl
  intro B _
  change (if A.map Embedding.some⊆B.map Embedding.some then _ else _) = _
  by_cases h : A⊆B
  · rw [if_pos (map_subset_map.mpr h),if_pos h]; rfl
  · rw [if_neg (fun hh => h (map_subset_map.mp hh)),if_neg h]

private theorem represents_some {r k : ℕ} {l : ℤ} {z : Finset (Option α) → ℤ} :
    Represents (punctured α) r k (fun _ => l) z ↔
      Represents univ r k (fun _ => l) (fun B => z (B.map Embedding.some)) := by
  constructor
  · intro h A hA
    rw [← incidence_map_some]
    apply h
    exact mem_powersetCard.mpr ⟨map_subset_map.mpr (subset_univ _),by simpa using (mem_powersetCard.mp hA).2⟩
  · intro h A hA
    rw [punctured,powersetCard_map] at hA
    obtain ⟨T,hT,rfl⟩ := mem_map.mp hA
    exact (incidence_map_some _ T _ z).trans (h T hT)

def indicator (H : Finset (Finset α)) (B : Finset α) : ℤ := if B∈H then 1 else 0

private theorem design_of_indicator {r k : ℕ} {H : Finset (Finset α)} (size : ∀ B∈H, B.card=k)
    (rows : Represents univ r k (fun _ => 1) (indicator H)) : H.IsBlockDesign r k := by
  refine ⟨size,fun A ha => ?_⟩
  let U := (univ.powersetCard k).filter (A⊆·)
  have sum := rows A (mem_powersetCard.mpr ⟨subset_univ _,ha⟩)
  have nc : ((U.filter (·∈H)).card:ℤ)=1 := by
    rw [card_filter,Nat.cast_sum]
    simpa [U,incidence,indicator] using sum
  obtain ⟨B,eq⟩ := card_eq_one.mp (show (U.filter (·∈H)).card=1 by exact_mod_cast nc)
  have unique (C : Finset α) : C∈H ∧ A⊆C ↔ C=B := by
    have hmem : C∈U.filter (·∈H) ↔ C∈H ∧ A⊆C := by
      simp only [U,mem_filter,mem_powersetCard,subset_univ,true_and]
      grind
    rw [← hmem,eq,mem_singleton]
  exact ⟨B,(unique B).mpr rfl,fun C hC => (unique C).mp hC⟩

private def oldWeight (H : Finset (Finset α)) (B : Finset (Option α)) := indicator H B.eraseNone

def extendedFamily (k : ℕ) (H : Finset (Finset α)) : Finset (Finset (Option α)) :=
  (univ.powersetCard (k+1)).filter fun B => extend none (punctured α) (oldWeight H) B=1

private theorem zero_one (H : Finset (Finset α)) (B : Finset (Option α)) :
    extend none (punctured α) (oldWeight H) B=0 ∨ extend none (punctured α) (oldWeight H) B=1 := by
  unfold extend oldWeight indicator
  split_ifs <;> simp

private theorem indicator_extend (H : Finset (Finset α)) {k : ℕ} {B : Finset (Option α)}
    (hb : B.card=k+1) : indicator (extendedFamily k H) B=extend none (punctured α) (oldWeight H) B := by
  obtain h|h := zero_one H B <;> simp [indicator,extendedFamily,h,hb]

/-- An explicit ordinary design with all the extended block incidences. -/
theorem extended_design {r k : ℕ} (hc : Fintype.card α=2*k+1) (hrk : r≤k) (even : Even r)
    {H : Finset (Finset α)} (hH : H.IsBlockDesign r k) :
    (extendedFamily k H).IsBlockDesign (r+1) (k+1) := by
  have h : Represents (punctured α) r k (fun _ => 1) (oldWeight H) := by
    apply represents_some.mpr
    simpa [oldWeight,indicator] using design_weights hH
  have he := extend_signed none_out (punctured_card.trans hc) hrk even h
  rw [add_point] at he
  apply design_of_indicator (fun _ hB => (mem_powersetCard.mp (mem_filter.mp hB).1).2)
  intro A hA
  exact (incidence_congr (fun _ hB => indicator_extend H (mem_powersetCard.mp hB).2) A).trans (he A hA)

/-- The derived family at the distinguished point is literally the input family. -/
theorem derived_membership {r k : ℕ} {H : Finset (Finset α)} (hH : H.IsBlockDesign r k) (B : Finset α) :
    insert none (B.map Embedding.some)∈extendedFamily k H ↔ B∈H := by
  have no : none∉B.map Embedding.some := by simp
  have hz : extend none (punctured α) (oldWeight H) (insert none (B.map Embedding.some))=indicator H B := by
    simp [extend,no,oldWeight]
  constructor
  · intro h
    have h' := (mem_filter.mp h).2
    rw [hz] at h'
    by_contra hn
    simp [indicator,hn] at h'
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,hz.trans (if_pos h)⟩
    rw [card_insert_of_notMem no,card_map,hH.1 B h]

/-- At odd block size and maximal punctured strength there is exactly one
ordinary extension on the labelled point set with this derived design. -/
theorem unique_steiner_extension {k : ℕ} (hc : Fintype.card α=2*k+1) (odd : Odd k)
    {H : Finset (Finset α)} (hH : H.IsBlockDesign (k-1) k) :
    ∃! G : Finset (Finset (Option α)), G.IsBlockDesign k (k+1) ∧
      ∀ B : Finset α, insert none (B.map Embedding.some)∈G ↔ B∈H := by
  have hk : 0<k := odd.pos
  have even : Even (k-1) := by obtain ⟨x,hx⟩ := odd; exact ⟨x,by omega⟩
  have same : k-1+1=k := by omega
  have hE : (extendedFamily k H).IsBlockDesign k (k+1) := same ▸ extended_design hc (by omega) even hH
  refine ⟨extendedFamily k H,⟨hE,derived_membership hH⟩,?_⟩
  rintro G ⟨hg,through⟩
  let V := punctured α
  have card : V.card=2*k+1 := punctured_card.trans hc
  have rep : Represents (insert none V) ((k+1)-1) (k+1) (fun _ => 1) (indicator G) := by
    rw [add_point,Nat.add_sub_cancel]
    exact design_weights hg
  have sym := automatic_symmetry (by omega) (odd.add_odd odd_one)
    (show (insert none V).card=2*(k+1) by rw [card_insert_of_notMem none_out,card]; omega) rep
  have der (A : Finset (Option α)) (ha : A∈V.powersetCard k) :
      indicator G (insert none A)=oldWeight H A := by
    have no : none∉A := fun h => none_out ((mem_powersetCard.mp ha).1 h)
    have eq := through A.eraseNone
    rw [map_some_eraseNone,erase_eq_of_notMem no] at eq
    unfold oldWeight indicator
    exact if_congr eq rfl rfl
  ext B
  by_cases size : B.card=k+1
  · have mem : B∈(insert none V).powersetCard (k+1) := by
      rw [add_point]
      exact mem_powersetCard.mpr ⟨subset_univ _,size⟩
    have eq := (unique_on_layer none_out card sym der B mem).trans (indicator_extend H size).symm
    by_cases h : B∈G <;> by_cases e : B∈extendedFamily k H <;> simp_all [indicator]
  · exact iff_of_false (fun h => size (hg.1 _ h)) (fun h => size (hE.1 _ h))

def derivedFamily (G : Finset (Finset (Option α))) : Finset (Finset α) :=
  (G.filter (none∈·)).image Finset.eraseNone

omit [Fintype α] in
theorem mem_derived {G : Finset (Finset (Option α))} {B : Finset α} :
    B∈derivedFamily G ↔ insert none (B.map Embedding.some)∈G := by
  constructor
  · intro h
    obtain ⟨C,hC,rfl⟩ := mem_image.mp h
    rw [map_some_eraseNone,insert_erase (mem_filter.mp hC).2]
    exact (mem_filter.mp hC).1
  · intro h
    let C := insert none (B.map Embedding.some)
    refine mem_image.mpr ⟨C,mem_filter.mpr ⟨h,mem_insert_self ..⟩,?_⟩
    ext x
    simp [C]

theorem derived_design {r k : ℕ} {G : Finset (Finset (Option α))} (hg : G.IsBlockDesign (r+1) (k+1)) :
    (derivedFamily G).IsBlockDesign r k := by
  have rep : Represents (insert (none : Option α) (punctured α)) (r+1) (k+1) (fun _ => 1) (indicator G) := by
    rw [add_point]
    exact design_weights hg
  have h := represents_some.mp (derive_signed none_out rep)
  apply design_of_indicator
  · intro B hB
    have hc := hg.1 _ (mem_derived.mp hB)
    simpa using hc
  · intro A hA
    apply Eq.trans (incidence_congr (w:=indicator (derivedFamily G)) (z:=fun B => indicator G (insert none (B.map Embedding.some))) (fun B _ => ?_) A) (h A hA)
    exact if_congr mem_derived rfl rfl

theorem mendelsohn_steiner_iff {k : ℕ} (hc : Fintype.card α=2*k+1) (odd : Odd k) :
    (∃ H : Finset (Finset α), H.IsBlockDesign (k-1) k) ↔
      ∃ G : Finset (Finset (Option α)), G.IsBlockDesign k (k+1) := by
  have hk := odd.pos
  constructor
  · rintro ⟨H,hH⟩
    obtain ⟨G,hG,_⟩ := unique_steiner_extension hc odd hH
    exact ⟨G,hG.1⟩
  · rintro ⟨G,hg⟩
    exact ⟨_,derived_design (r:=k-1) (by simpa only [show k-1+1=k by omega] using hg)⟩

#print axioms derivedFamily
#print axioms mem_derived
#print axioms derived_design
#print axioms mendelsohn_steiner_iff

#print axioms unique_steiner_extension

#print axioms punctured
#print axioms indicator
#print axioms extendedFamily
#print axioms extended_design
#print axioms derived_membership
end Erdos722.ComplementExtension
