import Green28UniformSums

/-! Integer averages forced by collisions throughout a row of a sum table. -/

open Finset Green28

namespace Green28AverageObstruction

/-- A row can be removed from a sumset with this opposite support. -/
def Covered (A : Set ℤ) (a : ℤ) (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∃ x ∈ A, x ≠ a ∧ ∃ c ∈ B, a+b=x+c

/-- The row is an average of at most `n` other sites. Repeated sites are allowed. -/
def ShortAverage (A : Set ℤ) (a : ℤ) (n : ℕ) : Prop :=
  ∃ t, 0<t ∧ t≤n ∧ ∃ f : ℕ → ℤ, (∀ i<t, f i∈A ∧ f i≠a) ∧
    ∑ i ∈ range t, f i = (t:ℤ)*a

/-- Iterating one competing representation at each column gives a cycle. -/
theorem average_of_covered {A : Set ℤ} {a : ℤ} {B : Finset ℤ}
    (nonempty : B.Nonempty) (cover : Covered A a B) : ShortAverage A a B.card := by
  classical
  obtain ⟨b₀,h₀⟩ := nonempty
  have step (b : B) : ∃ c : B, a+(b:ℤ)-(c:ℤ) ∈ A ∧ a+(b:ℤ)-(c:ℤ) ≠ a := by
    obtain ⟨x,hx,ne,c,hc,eq⟩ := cover b b.property
    exact ⟨⟨c,hc⟩,by simpa only [show a+(b:ℤ)-c=x by omega] using And.intro hx ne⟩
  let next (b : B) := (step b).choose
  let walk (i : ℕ) := next^[i] ⟨b₀,h₀⟩
  have hop (i : ℕ) : a+(walk i:ℤ)-(walk (i+1):ℤ)∈A ∧ a+(walk i:ℤ)-(walk (i+1):ℤ)≠a := by
    simpa only [walk,Function.iterate_succ_apply'] using (step (walk i)).choose_spec
  let tag (i : Fin (B.card+1)) := walk i.val
  obtain ⟨u,v,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by simp)
  have cycle {i j : ℕ} (lt : i<j) (bound : j≤B.card) (e : walk i=walk j) : ShortAverage A a B.card := by
    let f (k : ℕ) := a+(walk (i+k):ℤ)-(walk (i+k+1):ℤ)
    have total (t : ℕ) : ∑ k ∈ range t, f k = (t:ℤ)*a+(walk i:ℤ)-(walk (i+t):ℤ) := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [sum_range_succ,ih,Nat.cast_succ]
        dsimp only [f]
        change (t:ℤ)*a+(walk i:ℤ)-(walk (i+t):ℤ) + (a+(walk (i+t):ℤ)-(walk (i+t+1):ℤ)) =
          ((t:ℤ)+1)*a+(walk i:ℤ)-(walk (i+t+1):ℤ)
        ring
    refine ⟨j-i,by omega,by omega,f,fun k _ => hop (i+k),?_⟩
    rw [total,show i+(j-i)=j by omega,←e]
    ring
  rcases lt_or_gt_of_ne ne with l|l
  · exact cycle (show u.val<v.val from l) (by have := v.isLt; omega) eq
  · exact cycle (show v.val<u.val from l) (by have := u.isLt; omega) eq.symm

/-- The size bound is exact for the support question: partial sums of a
zero-sum sequence provide a finite opposite support on which the row is covered. -/
theorem exists_covered_iff {A : Set ℤ} {a : ℤ} {n : ℕ} :
    (∃ B : Finset ℤ, B.Nonempty ∧ B.card ≤ n ∧ Covered A a B) ↔ ShortAverage A a n := by
  constructor
  · rintro ⟨B,hB,bound,cover⟩
    obtain ⟨t,ht,le,f,hf,eq⟩ := average_of_covered hB cover
    exact ⟨t,ht,le.trans bound,f,hf,eq⟩
  · rintro ⟨t,ht,le,f,hf,eq⟩
    let pos (j : ℕ) := ∑ k ∈ range j, (a-f k)
    let B := (range t).image pos
    have endpt : pos t=pos 0 := by simp [pos,sum_sub_distrib,eq]
    refine ⟨B,⟨pos 0,mem_image.mpr ⟨0,mem_range.mpr ht,rfl⟩⟩,
      (card_image_le.trans (by simpa using le : (range t).card ≤ n)),?_⟩
    intro b hb
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
    have il := mem_range.mp hi
    have nxt : pos (i+1) ∈ B := by
      rcases lt_or_eq_of_le (by omega : i+1≤t) with h|h
      · exact mem_image.mpr ⟨i+1,mem_range.mpr h,rfl⟩
      · exact h ▸ endpt ▸ mem_image.mpr ⟨0,mem_range.mpr ht,rfl⟩
    refine ⟨f i,(hf _ il).1,(hf _ il).2,pos (i+1),nxt,?_⟩
    dsimp only [pos]; rw [sum_range_succ]; ring

private theorem sum_mass (P Q : PMF ℤ) (z : ℤ) :
    indepSum P Q z = ∑' x, P x * Q (z-x) := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
  rw [PMF.bind_apply]
  congr 1
  funext x
  rw [PMF.bind_apply, tsum_eq_single (z-x)]
  · simp [PMF.pure_apply]
  · intro y hy
    have h : z ≠ x+y := by omega
    simp [PMF.pure_apply,h]

/-- It suffices to follow collisions within any closed nonempty set of columns. -/
theorem average_of_nonmax_piece {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    {a : ℤ} (ha : a ∈ P.support) (below : ∃ x, P a < P x)
    (B : Finset ℤ) (nonempty : B.Nonempty) (sub : ∀ b∈B, b∈Q.support)
    (closed : ∀ b∈B, ∀ x∈P.support, a+b-x ∈ Q.support → a+b-x ∈ B) :
    ShortAverage P.support a B.card := by
  classical
  apply average_of_covered nonempty
  intro b hb
  obtain ⟨x,hx⟩ := below
  have xpos : x∈P.support := (P.mem_support_iff x).mpr (ne_of_gt ((bot_le : 0 ≤ P a).trans_lt hx))
  obtain ⟨S,hS,eq⟩ := uniform
  have flat {w} (hw : w∈P.support) : indepSum P Q (w+b)=(S.card:ENNReal)⁻¹ := by
    have z : w+b ∈ (indepSum P Q).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨w,hw,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨b,sub b hb,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rw [eq,PMF.support_uniformOfFinset] at z
    rw [eq,PMF.uniformOfFinset_apply_of_mem hS z]
  by_contra! alone
  have single : indepSum P Q (a+b)=P a*Q b := by
    rw [sum_mass,tsum_eq_single a]; · simp
    intro y ne
    by_cases py : y∈P.support
    · have miss : a+b-y ∉ Q.support := by
        intro cy
        exact alone y py ne (a+b-y) (closed b hb y py cy) (by omega)
      rw [(Q.apply_eq_zero_iff _).mpr miss,mul_zero]
    · rw [(P.apply_eq_zero_iff _).mpr py,zero_mul]
  have ub : P x * Q b ≤ indepSum P Q (x+b) := by
    rw [sum_mass]
    simpa only [add_sub_cancel_left] using
      (ENNReal.le_tsum (f := fun y => P y * Q (x+b-y)) x)
  rw [flat xpos,← flat ha,single] at ub
  exact hx.not_ge ((ENNReal.mul_le_mul_iff_left ((Q.mem_support_iff b).mp (sub b hb)) (Q.apply_ne_top b)).mp ub)

/-- Every left atom below maximal mass is an average of other left sites using
at most as many summands as there are occupied right sites. -/
theorem average_of_nonmax {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q))
    {a : ℤ} (ha : a ∈ P.support) (below : ∃ x, P a < P x) :
    ShortAverage P.support a Q.support.ncard := by
  obtain ⟨_,qf⟩ := Green28UniformSums.finite_of_uniform_sum u
  rw [Set.ncard_eq_toFinset_card _ qf]
  exact average_of_nonmax_piece u ha below qf.toFinset
    (by obtain ⟨b,hb⟩ := Q.support_nonempty; exact ⟨b,qf.mem_toFinset.mpr hb⟩)
    (fun _ hb => qf.mem_toFinset.mp hb) (fun _ _ _ _ hc => qf.mem_toFinset.mpr hc)

private theorem uniform_of_maximal {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q))
    (maxed : ∀ {a}, a∈P.support → ∀ x, P x ≤ P a) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply Green28UniformSums.uniform_of_rational_ratios u
  left
  intro x y hy
  by_cases hx : x∈P.support
  · have eq := le_antisymm (maxed hy x) (maxed hx y)
    exact ⟨1,by rw [eq,div_self (ENNReal.toReal_pos ((P.mem_support_iff _).mp hy) (P.apply_ne_top _)).ne']; simp⟩
  · exact ⟨0,by simp [(P.apply_eq_zero_iff _).mpr hx]⟩

/-- A uniform independent sum with a left support free of all short averages
forces both original laws to be uniform. -/
theorem uniform_of_no_short_average {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q))
    (free : ∀ a ∈ P.support, ¬ShortAverage P.support a Q.support.ncard) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_maximal u (fun ha x => le_of_not_gt (fun h => free _ ha (average_of_nonmax u ha ⟨x,h⟩)))

/-- A single isolated group of columns suffices for both conclusions. The other
occupied columns can be arbitrarily numerous. -/
theorem uniform_of_piece {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q))
    (B : Finset ℤ) (hb : B.Nonempty) (sub : ∀ b∈B, b∈Q.support)
    (closed : ∀ a∈P.support, ∀ b∈B, ∀ x∈P.support, a+b-x∈Q.support → a+b-x∈B)
    (free : ∀ a∈P.support, ¬ShortAverage P.support a B.card) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_maximal u (fun ha x => le_of_not_gt (fun h =>
    free _ ha (average_of_nonmax_piece u ha ⟨x,h⟩ B hb sub (closed _ ha))))

/-- Ordered positive sites separated by a factor exceeding the number of
summands cannot contain a short average. The origin can be translated freely. -/
theorem no_average_of_gaps {A : Set ℤ} {n : ℕ} (o : ℤ)
    (lower : ∀ x∈A, o≤x)
    (gap : ∀ a∈A, ∀ x∈A, a<x → (n:ℤ)*(a-o)<x-o) :
    ∀ a∈A, ¬ShortAverage A a n := by
  intro a ha ⟨t,ht,le,f,hf,total⟩
  have sum : ∑ i ∈ range t, (f i-o)=(t:ℤ)*(a-o) := by
    simp [sum_sub_distrib,total,mul_sub]
  have small (i) (hi : i∈range t) : f i < a := by
    obtain ⟨mem,ne⟩ := hf i (mem_range.mp hi)
    by_contra! ge
    have gt : a < f i := lt_of_le_of_ne ge ne.symm
    have hgap := gap a ha (f i) mem gt
    have positive (k) (hk : k∈range t) : 0 ≤ f k-o := sub_nonneg.mpr (lower _ (hf k (mem_range.mp hk)).1)
    have ub := single_le_sum (f := fun k => f k-o) positive hi
    rw [sum] at ub
    have m : (t:ℤ)*(a-o) ≤ (n:ℤ)*(a-o) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast le) (sub_nonneg.mpr (lower _ ha))
    omega
  have hlt := sum_lt_sum_of_nonempty (show (range t).Nonempty from ⟨0,mem_range.mpr ht⟩) (fun i hi => small i hi)
  simp only [sum_const,card_range,nsmul_eq_mul,total] at hlt
  omega

/-- A uniform sum with a sufficiently lacunary marginal is fair on both sides. -/
theorem uniform_of_gaps {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q)) (o : ℤ)
    (lower : ∀ x∈P.support, o≤x)
    (gap : ∀ a∈P.support, ∀ x∈P.support, a<x → (Q.support.ncard:ℤ)*(a-o)<x-o) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q :=
  uniform_of_no_short_average u (no_average_of_gaps o lower gap)

/-- One four-site family of unbounded diameter. It suffices that one group of
fewer than `N` opposite atoms is isolated under all occupied left differences. -/
theorem four_site_piece {P Q : PMF ℤ} (u : IsUniformOnSupport (indepSum P Q))
    (o N : ℤ) (sites : ∀ x∈P.support, x=o ∨ x=o+1 ∨ x=o+N ∨ x=o+N^2)
    (B : Finset ℤ) (hb : B.Nonempty) (sub : ∀ b∈B, b∈Q.support)
    (closed : ∀ a∈P.support, ∀ b∈B, ∀ x∈P.support, a+b-x∈Q.support → a+b-x∈B)
    (small : (B.card:ℤ)<N) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  have np : 0<(B.card:ℤ) := by exact_mod_cast card_pos.mpr hb
  have pos : 1<N := by omega
  have square : N<N^2 := by nlinarith
  have prod : (B.card:ℤ)*N < N^2 := by simpa [pow_two] using mul_lt_mul_of_pos_right small (by omega : 0<N)
  apply uniform_of_piece u B hb sub closed
  apply no_average_of_gaps o
  · intro x hx
    rcases sites x hx with rfl|rfl|rfl|rfl <;> omega
  · intro a ha x hx lt
    rcases sites a ha with rfl|rfl|rfl|rfl <;> rcases sites x hx with rfl|rfl|rfl|rfl <;>
      simp_all only [add_sub_cancel_left,sub_self,mul_zero,mul_one] <;> omega

#print axioms exists_covered_iff
#print axioms average_of_nonmax_piece
#print axioms average_of_nonmax
#print axioms uniform_of_no_short_average
#print axioms uniform_of_piece
#print axioms uniform_of_gaps
#print axioms four_site_piece

end Green28AverageObstruction
