theory trichotomy2
	imports Axioms Definitions Theorems
begin

theorem trichotomy2:
	assumes: `axioms`
		"seg_lt A B C D"
	shows: "\<not> (seg_lt C D A B)"
proof -
	obtain E where "bet C E D \<and> seg_eq C E A B" sorry
	have "bet C E D" using `bet C E D \<and> seg_eq C E A B` by blast
	have "seg_eq C E A B" using `bet C E D \<and> seg_eq C E A B` by blast
	have "seg_eq A B C E" using congruencesymmetric[OF `axioms` `seg_eq C E A B`] .
	have "\<not> (seg_lt C D A B)"
	proof (rule ccontr)
		assume "seg_lt C D A B"
		have "seg_lt C D C E" using lessthancongruence[OF `axioms` `seg_lt C D A B` `seg_eq A B C E`] .
		obtain F where "bet C F E \<and> seg_eq C F C D" sorry
		have "bet C F E" using `bet C F E \<and> seg_eq C F C D` by blast
		have "bet C F D" using n3_6b[OF `axioms` `bet C F E` `bet C E D`] .
		have "\<not> (seg_eq C F C D)" using partnotequalwhole[OF `axioms` `bet C F D`] .
		have "seg_eq C F C D" using `bet C F E \<and> seg_eq C F C D` by blast
		show "False" using `seg_eq C F C D` `\<not> (seg_eq C F C D)` by blast
	qed
	hence "\<not> (seg_lt C D A B)" by blast
	thus ?thesis by blast
qed

end