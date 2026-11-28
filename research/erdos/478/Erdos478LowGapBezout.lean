import Erdos478RegularGapPrimes

/-! # Integral Bézout certificates for factorial gap polynomials of degrees two through ten

Each row consists of a positive constant and the coefficients (constant term first)
of two polynomials U,V satisfying f U + f' V = c. Only the divisibility of c
needs to be checked at a sample prime. -/

namespace Erdos478.LocalWitness
open Polynomial SplittingDensity
noncomputable section

def lowCertificate : ℕ → ℕ × List ℤ × List ℤ
  | 2 => (5,
      [-4],
      [-1, 2])
  | 3 => (23,
      [-45, 18],
      [-11, 21, -6])
  | 4 => (28,
      [26, -120, 40],
      [-9, -39, 45, -10])
  | 5 => (38569,
      [112775, -359400, 250400, -44150],
      [6306, -101475, 154380, -67740, 8830])
  | 6 => (565573,
      [-583573, 2225160, -1931832, 594720, -59472],
      [150, 565715, -958965, 540862, -123900, 9912])
  | 7 => (613905133493513,
      [303786107019367, -1329171032666232, 1449438030292644, -624275664314708, 115683390321828,
       -7702107102172],
      [1274571167379, -299386779177913, 599840287034716, -421708106739360, 134359629553072,
       -19827101661192, 1100301014596])
  | 8 => (203295631264,
      [-43969140304, 210755502216, -266795034396, 143162427240, -37203580500, 4624747344, -220226064],
      [-31612399, 43763390867, -97516721400, 79842053559, -31642711170, 6529251171, -674442321,
       27528258])
  | 9 => (3896978231785054281230161833,
      [338400934710119915639493207, -1732836403915337602590086016, 2447043108585152988834937440,
       -1534587776342127124039056456, 498271340432211333301609488, -87107462919829119863510532,
       7774362487557520224305328, -277662543119065797896772],
      [105044126153154121946172, -337872921946309917003677023, 815118591866239600756327680,
       -747069529520143288180214144, 346128164935652275870357896, -89141827038257714726392224,
       12928203249918380974972596, -987223628892642601765824, 30851393679896199766308])
  | 10 => (1735005527043935158242581,
      [-55484871730738821896981, 299188987332093746870400, -459740019282986458526400,
       324492842135708000825400, -123865789379523237083400, 27187312379327176962600,
       -3428330917359797532600, 230608897317062985600, -6405802703251749600],
      [-4628308684174372620, 55457860569421410975353, -142330735968626901615975,
       142446937004472270692610, -74354992236510490697940, 22507792453432947931512,
       -4095009352993871743200, 441322308298475403360, -25943500948169585880, 640580270325174960])
  | _ => (0,[],[])

private def horner : List ℤ → ℤ[X]
  | [] => 0
  | a::as => (a:ℤ[X])+X*horner as

private def falling : ℕ → ℤ[X]
  | 0 => 1
  | k+1 => falling k*(X-(k:ℤ[X]))

private theorem falling_eq (k : ℕ) : descPochhammer ℤ k=falling k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [descPochhammer_succ_right,ih]; rfl

set_option maxHeartbeats 4000000 in
private theorem bezout_identity {k : ℕ} (lo : 2≤k) (hi : k≤10) :
    gapPoly k*horner (lowCertificate k).2.1+(gapPoly k).derivative*horner (lowCertificate k).2.2=
      ((lowCertificate k).1:ℤ[X]) := by
  rw [gapPoly,falling_eq]
  interval_cases k <;> norm_num [falling,horner,lowCertificate,derivative_mul] <;> ring

theorem low_gap_regular {k p : ℕ} [Fact p.Prime] (lo : 2≤k) (hi : k≤10)
    (hp : ¬p∣(lowCertificate k).1) : ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable := by
  let φ := Int.castRingHom (ZMod p)
  let c := (lowCertificate k).1
  let f := (gapPoly k).map φ
  let u := (horner (lowCertificate k).2.1).map φ
  let v := (horner (lowCertificate k).2.2).map φ
  have hd : (c:ZMod p)≠0 := fun h => hp ((ZMod.natCast_eq_zero_iff ..).mp h)
  have eq := congrArg (Polynomial.map φ) (bezout_identity lo hi)
  have he : f*u+f.derivative*v=C (c:ZMod p) := by
    simpa only [Polynomial.map_add,Polynomial.map_mul,← derivative_map,Polynomial.map_natCast,C_eq_natCast] using eq
  refine ⟨C (c:ZMod p)⁻¹*u,C (c:ZMod p)⁻¹*v,?_⟩
  change C (c:ZMod p)⁻¹*u*f+C (c:ZMod p)⁻¹*v*f.derivative=1
  calc
    _ = C (c:ZMod p)⁻¹*(f*u+f.derivative*v) := by ring
    _ = 1 := by rw [he,← C_mul,inv_mul_cancel₀ hd,C_1]

#print axioms lowCertificate
#print axioms low_gap_regular
end
end Erdos478.LocalWitness
