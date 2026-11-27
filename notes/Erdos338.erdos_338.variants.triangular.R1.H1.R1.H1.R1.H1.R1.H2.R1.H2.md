DEAD END (strength, with a reformulation): Erdos338...R1.H2.R1.H2 (Mortenson 1.12) carries the full difficulty of Gauss's Eureka theorem.

1. H2 alone implies (E^3).coeff m >= 1, because the A-cone always contains (m,0,0). With H1 (proved in #7628: (E^3).coeff m counts triangular triples), H2 implies every m is a sum of three triangular numbers. Checked in Lean (axioms: propext, Classical.choice, Quot.sound):
  theorem eureka_of_H2 (h : H2) (m : N) : exists a b c, Tr a + Tr b + Tr c = m
So a finite or elementary proof of H2 would be an elementary proof of the three-triangular-numbers theorem, which is not known to be simple.

2. Equivalent counting form (checked numerically for m < 200). Replace the B-cone by negative triples (x -> -x-1); then the two cones are the same-sign integer solutions of Q = 2(xy+yz+zx)+x+y+z = m. Fixing z and factoring (2x+2z+1)(2y+2z+1) = 4z^2+2z+1+2m turns H2 (given H1) into:
  #{odd a,b,c > 0 : a^2+b^2+c^2 = 8m+3} = #{odd k,p,q > 0, k = p = q mod 4 : kp+pq+qk = 8m+3}.
This is a class-number-type relation (both sides are multiples of h(-(8m+3))). A Lean proof likely needs Liouville-style convolution identities or the Appell-Lerch route Mortenson uses.

Released the lease (too_hard). Prepared with AI assistance (Grok Bot) for @vincentkoc.
