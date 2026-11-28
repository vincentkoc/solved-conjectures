import ThetaFourierBound

/-! The original theta double sum as a count of odd products, including zero divisors. -/
namespace Arxiv.«2501.03234».ThetaOddSquare
open Finset ThetaFourier
variable {p : ℕ} [NeZero p]

lemma odd_neg {a : ZMod p} (ha : a≠0) (hp : p%2=1) :
    (-a).val%2=1 ↔ ¬a.val%2=1 := by
  let : NeZero a := ⟨ha⟩
  rw [ZMod.val_neg_of_ne_zero]
  have := a.val_lt
  omega

lemma split_sign {M : Type*} [AddCommMonoid M] (hp : p%2=1) (f : ZMod p → M) :
    ∑ a∈univ.erase 0,f a = ∑ a∈odds p,(f a+f (-a)) := by
  classical
  let U := (univ : Finset (ZMod p)).erase 0
  have hO : U.filter (fun a => a.val%2=1)=odds p := by
    ext a
    simp only [U,odds,mem_filter,mem_erase,mem_univ,true_and,and_true]
    constructor
    · exact And.right
    · intro h; exact ⟨fun eq => by subst a; simp at h,h⟩
  change ∑ a∈U,f a=_
  rw [←sum_filter_add_sum_filter_not U (fun a => a.val%2=1) f,hO,sum_add_distrib]
  congr 1
  apply sum_nbij' (fun a => -a) (fun a => -a)
  · intro a ha
    obtain ⟨ha,he⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨mem_univ _,(odd_neg (mem_erase.mp ha).1 hp).2 he⟩
  · intro a ha
    have ho := (mem_filter.mp ha).2
    have hn : a≠0 := by rintro rfl; simp at ho
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨neg_ne_zero.mpr hn,mem_univ _⟩,
      fun h => (odd_neg hn hp).1 h ho⟩
  · simp
  · simp
  · simp

private def sign (a : ZMod p) : ℤ := if a.val%2=1 then 1 else -1
private def summand (h j : ZMod p) : ℤ := if j.val%2=1 then sign h*sign (h*j) else sign (h*j)

omit [NeZero p] in
private lemma theta_summand (hp : p%2=1) (h j : ZMod p) :
    (-1:ℤ)^(j.val+1+h.val*j.val/p)=summand h j := by
  have hr := ZMod.val_mul h j
  have he := congrArg (·%2) (Nat.mod_add_div (h.val*j.val) p)
  change (h.val*j.val%p+p*(h.val*j.val/p))%2=(h.val*j.val)%2 at he
  rw [←hr,Nat.add_mod,Nat.mul_mod p,hp,one_mul,Nat.mul_mod h.val j.val] at he
  simp only [neg_one_pow_eq_ite,Nat.even_iff,summand,sign]
  rcases Nat.mod_two_eq_zero_or_one h.val with hh|hh <;>
    rcases Nat.mod_two_eq_zero_or_one j.val with hj|hj <;>
    rcases Nat.mod_two_eq_zero_or_one (h*j).val with hr'|hr' <;>
    simp [hh,hj,hr'] at he ⊢ <;> omega

private theorem reflected (hp : p%2=1) {h j : ZMod p} (hh : h∈odds p) (hj : j∈odds p) :
    (summand h j+summand (-h) j)+(summand h (-j)+summand (-h) (-j))=2*sign (h*j) := by
  have ho := (mem_filter.mp hh).2
  have jo := (mem_filter.mp hj).2
  have hn : h≠0 := by rintro rfl; simp at ho
  have jn : j≠0 := by rintro rfl; simp at jo
  have hneg : ¬(-h).val%2=1 := fun a => (odd_neg hn hp).1 a ho
  have jneg : ¬(-j).val%2=1 := fun a => (odd_neg jn hp).1 a jo
  simp only [summand,jo,jneg,if_true,if_false,neg_mul,mul_neg,neg_neg]
  rw [show sign h=1 from if_pos ho,show sign (-h)= -1 from if_neg hneg]
  ring

/-- Simultaneous reflection of both coordinates works when their product is zero as well. -/
theorem S_eq_odd_square (hp : p%2=1) :
    S p=2*∑ j∈odds p,∑ h∈odds p,sign (h*j) := by
  have reindex (f : ℕ → ℤ) : ∑ n∈Ico 1 p,f n=∑ a∈univ.erase (0:ZMod p),f a.val := by
    rw [sum_nonzero (p:=p) (fun a => f a.val)]
    exact sum_congr rfl (fun n hn => by rw [ZMod.val_natCast_of_lt (mem_Ico.mp hn).2])
  simp only [S,S',←Nat.cast_mul,Nat.floor_div_eq_div]
  rw [sum_comm,reindex]
  simp_rw [reindex,theta_summand hp,split_sign hp]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [←sum_add_distrib,mul_sum]
  exact sum_congr rfl (fun h hh => reflected hp hh hj)

/-- The canonical sum equals a count of products in the odd half of the residue ring. -/
theorem S_triples (hp : p%2=1) :
    (S p:ℂ)=4*triples (odds p)-2*((odds p).card:ℂ)^2 := by
  have he (x : ZMod p) : (sign x:ℂ)=2*(if x∈odds p then 1 else 0)-1 := by
    by_cases h : x.val%2=1 <;> norm_num [sign,odds,h]
  rw [S_eq_odd_square hp]
  push_cast
  simp only [he,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one,triples]
  rw [sum_comm (f:=fun a b : ZMod p => (if a*b∈odds p then (1:ℂ) else 0))]
  ring

#print axioms split_sign
#print axioms S_triples
end Arxiv.«2501.03234».ThetaOddSquare
