theory extensionunique
	imports Axioms Definitions Theorems
begin

theorem extensionunique:
	assumes: `axioms`
		"bet A B E"
		"bet A B F"
		"seg_eq B E B F"
	shows: "E = F"
proof -
	have "seg_eq B E B E" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B F B E" using congruencesymmetric[OF `axioms` `seg_eq B E B F`] .
	have "seg_eq A E A E" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq A B A B" using congruencereflexiveE[OF `axioms`] .
	have "seg_eq B E B F" using congruencesymmetric[OF `axioms` `seg_eq B F B E`] .
	have "seg_eq E E E F" using 5-lineE[OF `axioms` `seg_eq B E B F` `seg_eq A E A E` `seg_eq B E B E` `bet A B E` `bet A B F` `seg_eq A B A B`] .
	have "seg_eq E F E E" using congruencesymmetric[OF `axioms` `seg_eq E E E F`] .
	have "E = F" using nullsegment1E[OF `axioms` `seg_eq E F E E`] .
	thus ?thesis by blast
qed

end