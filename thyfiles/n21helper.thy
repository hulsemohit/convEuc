theory n21helper
	imports Axioms Definitions Theorems
begin

theorem n21helper:
	assumes: `axioms`
		"seg_sum_gt B A A E B E"
		"bet A E C"
	shows: "seg_sum_pair_gt B A A C B E E C"
proof -
	obtain H where "bet B A H \<and> seg_eq A H A E \<and> seg_lt B E B H" sorry
	have "bet B A H" using `bet B A H \<and> seg_eq A H A E \<and> seg_lt B E B H` by blast
	have "B \<noteq> A" using betweennotequal[OF `axioms` `bet B A H`] by blast
	have "seg_eq A H A E" using `bet B A H \<and> seg_eq A H A E \<and> seg_lt B E B H` by blast
	have "seg_lt B E B H" using `bet B A H \<and> seg_eq A H A E \<and> seg_lt B E B H` by blast
	have "\<not> (B = E)"
	proof (rule ccontr)
		assume "B = E"
		have "seg_lt B B B H" sorry
		obtain K where "bet B K H \<and> seg_eq B K B B" sorry
		have "bet B K H" using `bet B K H \<and> seg_eq B K B B` by blast
		have "seg_eq B K B B" using `bet B K H \<and> seg_eq B K B B` by blast
		have "B = K" using nullsegment1E[OF `axioms` `seg_eq B K B B`] .
		have "bet B B H" sorry
		have "B \<noteq> B" using betweennotequal[OF `axioms` `bet B B H`] by blast
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		show "False" using `B = B` `B \<noteq> B` by blast
	qed
	hence "B \<noteq> E" by blast
	have "A \<noteq> C" using betweennotequal[OF `axioms` `bet A E C`] by blast
	obtain F where "bet B A F \<and> seg_eq A F A C" using extensionE[OF `axioms` `B \<noteq> A` `A \<noteq> C`]  by  blast
	have "bet B A F" using `bet B A F \<and> seg_eq A F A C` by blast
	have "seg_eq A F A C" using `bet B A F \<and> seg_eq A F A C` by blast
	have "E \<noteq> C" using betweennotequal[OF `axioms` `bet A E C`] by blast
	obtain G where "bet B E G \<and> seg_eq E G E C" using extensionE[OF `axioms` `B \<noteq> E` `E \<noteq> C`]  by  blast
	have "seg_eq E G E C" using `bet B E G \<and> seg_eq E G E C` by blast
	have "seg_eq A C A F" using congruencesymmetric[OF `axioms` `seg_eq A F A C`] .
	have "seg_eq A E A H" using congruencesymmetric[OF `axioms` `seg_eq A H A E`] .
	have "seg_eq A E A E" using congruencereflexiveE[OF `axioms`] .
	have "seg_lt A E A C" sorry
	have "seg_lt A E A F" using lessthancongruence[OF `axioms` `seg_lt A E A C` `seg_eq A C A F`] .
	have "seg_lt A H A F" using lessthancongruence2[OF `axioms` `seg_lt A E A F` `seg_eq A E A H`] .
	have "ray_on A H F" sorry
	have "bet A H F" using lessthanbetween[OF `axioms` `seg_lt A H A F` `ray_on A H F`] .
	have "seg_eq E C H F" using differenceofparts[OF `axioms` `seg_eq A E A H` `seg_eq A C A F` `bet A E C` `bet A H F`] .
	have "seg_eq E G H F" using congruencetransitive[OF `axioms` `seg_eq E G E C` `seg_eq E C H F`] .
	have "seg_lt B E B H" using `seg_lt B E B H` .
	have "bet B E G" using `bet B E G \<and> seg_eq E G E C` by blast
	have "bet B A H" using `bet B A H` .
	have "bet A H F" using `bet A H F` .
	have "bet B H F" using n3_7a[OF `axioms` `bet B A H` `bet A H F`] .
	have "seg_lt B G B F" using lessthanadditive[OF `axioms` `seg_lt B E B H` `bet B E G` `bet B H F` `seg_eq E G H F`] .
	have "seg_sum_gt B A A C B G" sorry
	have "seg_sum_pair_gt B A A C B E E C" sorry
	thus ?thesis by blast
qed

end