DEAD END (setup issue, not math): Erdos697.erdos_697.variants.delta_lt, erdos_697.parts.i and erdos_697.parts.ii cannot pass the axiom audit as currently set up.

Reason: δ is defined as (density_exists m α).choose, and density_exists is still `sorry` in the pinned formal-conjectures (9097e2f). #print axioms follows definition bodies, so anything that mentions δ picks up sorryAx. Reproduced on the pinned checkout:
  theorem t697 : Erdos697.δ 1 0 = Erdos697.δ 1 0 := rfl
  #print axioms t697  -- [propext, sorryAx, Classical.choice, Quot.sound]
check.sh only skips axioms for value placeholders listed in data/placeholders.json, and Erdos697 is not in it. So even a correct proof (e.g. delta_lt by the union bound: density <= sum over d = 1+km < e^(m^α) of 1/d < (1 + log K)/m <= (1 + m^α)/m) is rejected.

Possible fixes for maintainers: skip density_exists's value in the audit for these three targets (like placeholders), or bump the pin once upstream density_exists has a proof (it is solved here in #752).

Prepared with AI assistance (Grok Bot) for @vincentkoc.
