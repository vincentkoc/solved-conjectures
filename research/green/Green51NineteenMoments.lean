import Green51ElevenQuadratic

/-! # Three moments obstruct a length-nineteen binary code -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51ElevenDimensions
local notation "F" => ZMod 2

/-- First three binomial moments of a length-19 code with eight as minimum distance
and without words of weight sixteen. -/
theorem enumerator_19 (a b c d e : ℕ)
    (total:1+a+b+c+d+e=128)
    (first:8*a+10*b+12*c+14*d+18*e=1216)
    (second:28*a+45*b+66*c+91*d+153*e=5472)
    (third:56*a+120*b+220*c+364*d+816*e=15504) :
    a=75 ∧ b=10 ∧ c=36 ∧ d=6 ∧ e=0 := by omega


def weight {n:ℕ} (v:Cube n) := (supp v).card

theorem binomial_moment {n:ℕ} (C:Submodule F (Cube n)) (k:ℕ) :
    ∑ c:C,(weight c.val).choose k =
      ∑ T∈(univ:Finset (Fin n)).powersetCard k,(univ.filter (fun c:C=>T⊆supp c.val)).card := by
  classical
  calc
    _ = ∑ c:C,∑ T∈(univ:Finset (Fin n)).powersetCard k,if T⊆supp c.val then (1:ℕ) else 0 := by
      apply sum_congr rfl
      intro c _
      rw [sum_boole]
      have eq:((univ:Finset (Fin n)).powersetCard k).filter (·⊆supp c.val)=
          (supp c.val).powersetCard k := by ext T;simp [mem_powersetCard,and_comm]
      rw [eq,card_powersetCard,weight];simp
    _ = _ := by rw [sum_comm];simp [sum_boole]

def allowedWeights : Finset ℕ := {0,8,10,12,14,18}
private noncomputable def multiplicity (C:Submodule F (Cube 19)) (j:ℕ) := (univ.filter (fun c:C=>weight c.val=j)).card

theorem sum_weights (C:Submodule F (Cube 19)) (allowed:∀c:C,weight c.val∈allowedWeights) (g:ℕ→ℕ) :
    (∑ c:C,g (weight c.val)) = g 0*multiplicity C 0+g 8*multiplicity C 8+
      g 10*multiplicity C 10+g 12*multiplicity C 12+g 14*multiplicity C 14+g 18*multiplicity C 18 := by
  classical
  calc
    _ = ∑ c:C,∑ j∈allowedWeights,if weight c.val=j then g j else 0 := by
      apply sum_congr rfl
      intro c _
      simp [allowed c]
    _ = ∑ j∈allowedWeights,g j*multiplicity C j := by
      rw [sum_comm];apply sum_congr rfl
      intro j _
      simp [multiplicity,sum_ite,mul_comm]
    _ = _ := by simp [allowedWeights,add_assoc]

/-- A seven-dimensional even code with uniform restrictions to triples cannot have
all its weights in the six allowedWeights left by three-space avoidance. -/
theorem code_obstruction (C:Submodule F (Cube 19)) (size:Fintype.card C=128)
    (allowed:∀c:C,weight c.val∈allowedWeights)
    (strength: ∀ k∈({1,2,3}:Finset ℕ), ∀ T∈(univ:Finset (Fin 19)).powersetCard k,
      (univ.filter (fun c:C=>T⊆supp c.val)).card=2^(7-k)) : False := by
  classical
  have mu0:multiplicity C 0=1 := by
    change (univ.filter (fun c:C=>weight c.val=0)).card=1
    have eq:univ.filter (fun c:C=>weight c.val=0)={0} := by
      ext c
      simp only [mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro h
        apply Subtype.ext;funext i
        have empty:=Finset.card_eq_zero.mp h
        by_contra! hn
        have mem:i∈supp c.val:=mem_filter.mpr ⟨mem_univ _,hn⟩
        rw [empty] at mem;exact (notMem_empty i) mem
      · rintro rfl;simp [weight,supp]
    rw [eq,card_singleton]
  have moment (k:ℕ) (hk:k∈({1,2,3}:Finset ℕ)) :
      (∑ c:C,(weight c.val).choose k)=(19:ℕ).choose k*2^(7-k) := by
    rw [binomial_moment]
    calc
      _ = ∑ _T∈(univ:Finset (Fin 19)).powersetCard k,2^(7-k) := sum_congr rfl (strength k hk)
      _ = _ := by simp [card_powersetCard]
  have m0:=sum_weights C allowed (fun _=>1)
  simp only [sum_const,card_univ,smul_eq_mul,mul_one,one_mul,mu0,size] at m0
  have mi (k:ℕ) (hk:k∈({1,2,3}:Finset ℕ)) := (moment k hk).symm.trans (sum_weights C allowed (·.choose k))
  have first:=mi 1 (by decide)
  have second:=mi 2 (by decide)
  have third:=mi 3 (by decide)
  norm_num [Nat.choose,mu0] at first second third
  obtain ⟨_,ten,_,fourteen,eighteen⟩:=enumerator_19 _ _ _ _ _ m0.symm first.symm second.symm third.symm
  let q:C→F:=fun c=>pairParity c.val
  let S:Finset C:=univ.filter (fun c=>q c=1)
  have sizeS:S.card=16 := by
    have eq:=sum_weights C allowed (fun k=>if (k.choose 2:F)=1 then 1 else 0)
    have count:S.card=∑ c:C,if ((weight c.val).choose 2:F)=1 then (1:ℕ) else 0 := by
      change (univ.filter _).card=_
      rw [Finset.card_filter]
      apply sum_congr rfl
      intro c _
      by_cases h:((supp c.val).card.choose 2:F)=1 <;> simp [q,pairParity_eq,weight,h]
    rw [count,eq]
    simp [ten,fourteen,eighteen,
      show ((8:ℕ).choose 2:F)≠1 by decide,
      show ((10:ℕ).choose 2:F)=1 by decide,show ((12:ℕ).choose 2:F)≠1 by decide,
      show ((14:ℕ).choose 2:F)=1 by decide]
  obtain ⟨a,ha⟩:=card_pos.mp (show 0<S.card by omega)
  have q0:q 0=0:=by simp [q,pairParity_eq,supp]
  have cap:=quadratic_quarter q q0 ⟨a,(mem_filter.mp ha).2⟩
    (fun x a b=>pairParity_second x.val a.val b.val)
  change Fintype.card C≤4*S.card at cap
  omega

end Green51ElevenDimensions

#print axioms Green51ElevenDimensions.enumerator_19
#print axioms Green51ElevenDimensions.binomial_moment
#print axioms Green51ElevenDimensions.code_obstruction
