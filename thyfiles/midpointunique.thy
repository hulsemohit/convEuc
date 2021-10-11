theory midpointunique
	imports Geometry congruenceflip congruencesymmetric lessthancongruence lessthantransitive partnotequalwhole
begin

theorem(in euclidean_geometry) midpointunique:
	assumes 
		"midpoint A B C"
		"midpoint A D C"
	shows "B = D"
proof -
	have "bet A B C \<and> seg_eq A B B C" using midpoint_f[OF `midpoint A B C`] .
	have "bet A D C \<and> seg_eq A D D C" using midpoint_f[OF `midpoint A D C`] .
	have "bet A B C" using `bet A B C \<and> seg_eq A B B C` by blast
	have "bet A D C" using `bet A D C \<and> seg_eq A D D C` by blast
	have "seg_eq A B B C" using `bet A B C \<and> seg_eq A B B C` by blast
	have "seg_eq A D D C" using `bet A D C \<and> seg_eq A D D C` by blast
	have "seg_eq A B A B" using congruencereflexiveE.
	have "\<not> (bet C D B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet C D B))"
hence "bet C D B" by blast
		have "bet B D C" using betweennesssymmetryE[OF `bet C D B`] .
		have "bet A B D" using innertransitivityE[OF `bet A B C` `bet B D C`] .
		have "seg_lt A B A D" using lessthan_b[OF `bet A B D` `seg_eq A B A B`] .
		have "seg_eq A D C D" using congruenceflip[OF `seg_eq A D D C`] by blast
		have "seg_lt A B C D" using lessthancongruence[OF `seg_lt A B A D` `seg_eq A D C D`] .
		have "bet C D B" using betweennesssymmetryE[OF `bet B D C`] .
		have "seg_eq C D C D" using congruencereflexiveE.
		have "seg_lt C D C B" using lessthan_b[OF `bet C D B` `seg_eq C D C D`] .
		have "seg_lt A B C B" using lessthantransitive[OF `seg_lt A B C D` `seg_lt C D C B`] .
		have "seg_eq C B B C" using equalityreverseE.
		have "seg_lt A B B C" using lessthancongruence[OF `seg_lt A B C B` `seg_eq C B B C`] .
		have "seg_eq B C A B" using congruencesymmetric[OF `seg_eq A B B C`] .
		have "seg_lt A B A B" using lessthancongruence[OF `seg_lt A B B C` `seg_eq B C A B`] .
		obtain E where "bet A E B \<and> seg_eq A E A B" using lessthan_f[OF `seg_lt A B A B`]  by  blast
		have "bet A E B" using `bet A E B \<and> seg_eq A E A B` by blast
		have "seg_eq A E A B" using `bet A E B \<and> seg_eq A E A B` by blast
		have "\<not> (seg_eq A E A B)" using partnotequalwhole[OF `bet A E B`] .
		show "False" using `\<not> (seg_eq A E A B)` `bet A E B \<and> seg_eq A E A B` by blast
	qed
	hence "\<not> (bet C D B)" by blast
	have "\<not> (bet C B D)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet C B D))"
hence "bet C B D" by blast
		have "bet D B C" using betweennesssymmetryE[OF `bet C B D`] .
		have "bet A D B" using innertransitivityE[OF `bet A D C` `bet D B C`] .
		have "seg_eq A D A D" using congruencereflexiveE.
		have "seg_lt A D A B" using lessthan_b[OF `bet A D B` `seg_eq A D A D`] .
		have "seg_eq A B B C" using `seg_eq A B B C` .
		have "seg_eq A B C B" using congruenceflip[OF `seg_eq A B B C`] by blast
		have "seg_lt A D C B" using lessthancongruence[OF `seg_lt A D A B` `seg_eq A B C B`] .
		have "bet C B D" using betweennesssymmetryE[OF `bet D B C`] .
		have "seg_eq C B C B" using congruencereflexiveE.
		have "seg_lt C B C D" using lessthan_b[OF `bet C B D` `seg_eq C B C B`] .
		have "seg_lt A D C D" using lessthantransitive[OF `seg_lt A D C B` `seg_lt C B C D`] .
		have "seg_eq D C A D" using congruencesymmetric[OF `seg_eq A D D C`] .
		have "seg_eq C D A D" using congruenceflip[OF `seg_eq D C A D`] by blast
		have "seg_lt A D C D" using `seg_lt A D C D` .
		have "seg_lt A D A D" using lessthancongruence[OF `seg_lt A D C D` `seg_eq C D A D`] .
		obtain F where "bet A F D \<and> seg_eq A F A D" using lessthan_f[OF `seg_lt A D A D`]  by  blast
		have "bet A F D" using `bet A F D \<and> seg_eq A F A D` by blast
		have "seg_eq A F A D" using `bet A F D \<and> seg_eq A F A D` by blast
		have "\<not> (seg_eq A F A D)" using partnotequalwhole[OF `bet A F D`] .
		show "False" using `\<not> (seg_eq A F A D)` `bet A F D \<and> seg_eq A F A D` by blast
	qed
	hence "\<not> (bet C B D)" by blast
	have "bet C D A" using betweennesssymmetryE[OF `bet A D C`] .
	have "bet C B A" using betweennesssymmetryE[OF `bet A B C`] .
	have "B = D" using connectivityE[OF `bet C B A` `bet C D A` `\<not> (bet C B D)` `\<not> (bet C D B)`] .
	thus ?thesis by blast
qed

end