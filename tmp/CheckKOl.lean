import PartitionsLeanblueprint.RamanujanCongruence.AiAssisted.KOl.Defs

#print axioms KOl.theta_filtration_drop_classification
#print axioms KOl.theta_half_cycle_filtration
#print axioms KOl.proposition_three_modular
#print axioms KOl.theorem_three
#print axioms KOl.kiming_olsson_theorem_one
#print axioms KOl.ramanujan_congruence_unique

example : KOl.partition 0 = 1 := KOl.partition_zero
example : KOl.partition (-1) = 0 := by simp [KOl.partition, KOl.standardPartition]
