import Green51DualCounts

/-! # Weight distributions of the shortened relation spaces -/

open Finset Green50Downsets Green50Sharp Green51WeightTransform
open scoped Classical
namespace Green51ShortenedProfiles
local notation "F" => ZMod 2

/-- The multiplicity of a binary relation weight. -/
noncomputable def multiplicity {n : ℕ} (C : Submodule F (Cube n)) (j : ℕ) :=
  (univ.filter fun c:C => (supp c.val).card=j).card

private theorem zero_count {n : ℕ} (C : Submodule F (Cube n)) : multiplicity C 0=1 := by
  have eq : (univ.filter fun c:C => (supp c.val).card=0)={0} := by
    ext c
    simp only [mem_filter,mem_univ,true_and,mem_singleton,card_eq_zero]
    constructor
    · intro h
      apply Subtype.ext
      funext i
      by_contra! ne
      have hit : i∈supp c.val := mem_filter.mpr ⟨mem_univ _,ne⟩
      rw [h] at hit
      exact notMem_empty i hit
    · rintro rfl; simp [supp]
  rw [multiplicity,eq,card_singleton]

private abbrev weights : Finset ℕ := {0,8,12,16}

private theorem sum_code {n : ℕ} (C : Submodule F (Cube n))
    (allowed : ∀ c:C,(supp c.val).card∈weights) (g : ℕ→ℤ) :
    (∑ c:C,g (supp c.val).card) = g 0+g 8*multiplicity C 8+g 12*multiplicity C 12+
      g 16*multiplicity C 16 := by
  calc
    _ = ∑ c:C,∑ j∈weights,if (supp c.val).card=j then g j else 0 := by
      apply sum_congr rfl; intro c _
      simp [allowed c]
    _ = ∑ j∈weights,g j*multiplicity C j := by
      rw [sum_comm];apply sum_congr rfl;intro j _
      simp [multiplicity,sum_ite,mul_comm]
    _ = _ := by simp [weights,zero_count,add_assoc]

private def row (n:ℕ) (S:Finset ℕ) : ℤ×ℤ×ℤ×ℤ :=
  let k w := ∑ j∈S,coefficient n w j
  (k 0,k 8,k 12,k 16)

private def lin (r:ℤ×ℤ×ℤ×ℤ) (a b c:ℕ) : ℤ := r.1+r.2.1*a+r.2.2.1*b+r.2.2.2*c

/-- Primal multiplicities at 8, 12 and 16, followed by the dual multiplicity
at 3 and the total number of dual words of weight 3 modulo 4. -/
def profiles (n:ℕ) : Finset (ℕ×ℕ×ℕ×ℕ×ℕ) :=
  match n with
  | 18 => {(45,18,0,6,768),(46,16,1,0,768)}
  | 19 => {(78,48,1,1,768)}
  | 20 => {(130,120,5,0,1024)}
  | 21 => {(210,280,21,0,1536)}
  | 22 => {(330,616,77,0,2048)}
  | 23 => {(506,1288,253,0,2048)}
  | _ => ∅

private def threes : Finset ℕ := {3,7,11,15,19,23}

private def table (n:ℕ) : (ℤ×ℤ×ℤ×ℤ)×(ℤ×ℤ×ℤ×ℤ)×(ℤ×ℤ×ℤ×ℤ)×(ℤ×ℤ×ℤ×ℤ) :=
  match n with
  | 18 => ((18,2,-6,-14),(153,-7,9,89),(816,-16,16,-336),(65280,-256,-256,-256))
  | 19 => ((19,3,-5,-13),(171,-5,3,75),(969,-23,25,-247),(130816,-256,-256,-256))
  | 20 => ((20,4,-4,-12),(190,-2,-2,62),(1140,-28,28,-172),(262144,0,0,0))
  | 21 => ((21,5,-3,-11),(210,2,-6,50),(1330,-30,26,-110),(524800,512,512,512))
  | 22 => ((22,6,-2,-10),(231,7,-9,39),(1540,-28,20,-60),(1049600,1024,1024,1024))
  | 23 => ((23,7,-1,-9),(253,13,-11,29),(1771,-21,11,-21),(2098176,1024,1024,1024))
  | _ => 0

private theorem table_eq (n:ℕ) (lo:18≤n) (hi:n≤23) :
    row n {1}=(table n).1 ∧ row n {2}=(table n).2.1 ∧
    row n {3}=(table n).2.2.1 ∧ row n threes=(table n).2.2.2 := by
  interval_cases n <;> decide +kernel

private theorem arithmetic (n a b c d s b₂:ℕ) (lo:18≤n) (hi:n≤23)
    (total:1+a+b+c=2^(n-12))
    (one:lin (row n {1}) a b c=0)
    (two:lin (row n {2}) a b c=(2:ℤ)^(n-12)*b₂)
    (two_zero:19≤n → b₂=0)
    (three:lin (row n {3}) a b c=(2:ℤ)^(n-12)*d)
    (cosets:lin (row n threes) a b c=(2:ℤ)^(n-12)*s) :
    (a,b,c,d,s)∈profiles n := by
  obtain ⟨r₁,r₂,r₃,r₄⟩ := table_eq n lo hi
  rw [r₁] at one
  rw [r₂] at two
  rw [r₃] at three
  rw [r₄] at cosets
  interval_cases n <;> norm_num [lin,profiles,table] at * <;> omega

/-- All relation and short dual multiplicities required for one-label extension. -/
theorem profile {n:ℕ} (C:Submodule F (Cube n)) (lo:18≤n) (hi:n≤23)
    (rank:n-12≤Module.finrank F C) (allowed:∀ c:C,(supp c.val).card∈({0,8,12,16}:Finset ℕ)) :
    (multiplicity C 8,multiplicity C 12,multiplicity C 16,
      ((dualWords C).filter fun z=>(supp z).card=3).card,
      ((dualWords C).filter fun z=>(supp z).card%4=3).card)∈profiles n := by
  classical
  have wt0 {x:Cube n} (w:(supp x).card=0) : x=0 := by
    funext i
    by_contra! ne
    have hit : i∈supp x := mem_filter.mpr ⟨mem_univ _,ne⟩
    rw [card_eq_zero.mp w] at hit
    exact notMem_empty i hit
  have al (c:C) := allowed c
  simp only [mem_insert,mem_singleton] at al
  have dist (c:C) (nz:c≠0) : 8≤(supp c.val).card := by
    have h:=al c
    have non : (supp c.val).card≠0 := fun w=>nz (Subtype.ext (wt0 w))
    omega
  have four (c:C) : 4∣(supp c.val).card := by have h:=al c;omega
  obtain ⟨dim,onto⟩ := Green51ResidualPacking.projection (by omega) C rank dist four
  have size := Module.card_eq_pow_finrank (K:=F) (V:=C)
  rw [dim,ZMod.card] at size
  have vanish {j:ℕ} (pos:0<j) (h:j≤n-17) : ((dualWords C).filter (fun z=>(supp z).card=j)).card=0 := by
    rw [card_eq_zero,eq_empty_iff_forall_notMem]
    intro z mem
    obtain ⟨hz,sz⟩:=mem_filter.mp mem
    have zero:=no_small_dual C onto hz (sz ▸ h)
    simp [zero,supp] at sz
    omega
  have transform (S:Finset ℕ) :
      lin (row n S) (multiplicity C 8) (multiplicity C 12) (multiplicity C 16)=
        (2:ℤ)^(n-12)*((dualWords C).filter fun z=>(supp z).card∈S).card := by
    have h:=dual_count C (fun c=>by rw [even_iff_two_dvd];exact dvd_trans (by decide : 2∣4) (four c)) S
    rw [sum_code C allowed (fun w=>∑ j∈S,coefficient n w j),size] at h
    push_cast at h
    exact h.symm
  have count:=sum_code C allowed (fun _=>1)
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,one_mul,size] at count
  have singles (j:ℕ) := transform {j}
  simp only [mem_singleton] at singles
  have one := singles 1
  rw [vanish (by decide) (by omega),Nat.cast_zero,mul_zero] at one
  have three := transform threes
  have eq:((dualWords C).filter fun z=>(supp z).card∈threes)=
      ((dualWords C).filter fun z=>(supp z).card%4=3) := by
    apply filter_congr;intro z _
    have upper: (supp z).card≤n := (supp z).card_le_univ.trans_eq (by simp)
    simp only [threes,mem_insert,mem_singleton];omega
  rw [eq] at three
  apply arithmetic n _ _ _ _ _ _ lo hi _ one (singles 2) (fun hn=>vanish (by decide) (by omega)) (singles 3) three
  exact_mod_cast count.symm

end Green51ShortenedProfiles
#print axioms Green51ShortenedProfiles.profile
