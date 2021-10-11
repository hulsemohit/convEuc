theory subtractequals
	imports n3_6a n3_6b Geometry betweennotequal congruencesymmetric layoffunique lessthancongruence lessthantransitive ray4 sumofparts trichotomy2
begin

theorem(in euclidean_geometry) subtractequals:
	assumes 
		"bet A B C"
		"bet A D E"
		"seg_eq B C D E"
		"bet A C E"
	shows "bet A B D"
proof -
	have "\<not> (bet A D B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (bet A D B))"
hence "bet A D B" by blast
		have "bet A D C" using n3_6b[OF `bet A D B` `bet A B C`] .
		have "bet A D C" using n3_6b[OF `bet A D B` `bet A B C`] .
		have "bet B C E" using n3_6a[OF `bet A B C` `bet A C E`] .
		have "seg_eq B C B C" using congruencereflexiveE.
		have "seg_lt B C B E" using lessthan_b[OF `bet B C E` `seg_eq B C B C`] .
		have "seg_eq B E E B" using equalityreverseE.
		have "seg_lt B C E B" using lessthancongruence[OF `seg_lt B C B E` `seg_eq B E E B`] .
		have "bet D C E" using n3_6a[OF `bet A D C` `bet A C E`] .
		have "bet D B C" using n3_6a[OF `bet A D B` `bet A B C`] .
		have "bet D B E" using n3_6b[OF `bet D B C` `bet D C E`] .
		have "bet E B D" using betweennesssymmetryE[OF `bet D B E`] .
		have "seg_eq E B E B" using congruencereflexiveE.
		have "seg_lt E B E D" using lessthan_b[OF `bet E B D` `seg_eq E B E B`] .
		have "seg_eq E D D E" using equalityreverseE.
		have "seg_lt E B D E" using lessthancongruence[OF `seg_lt E B E D` `seg_eq E D D E`] .
		have "seg_lt B C D E" using lessthantransitive[OF `seg_lt B C E B` `seg_lt E B D E`] .
		have "seg_eq D E B C" using congruencesymmetric[OF `seg_eq B C D E`] .
		have "seg_lt B C B C" using lessthancongruence[OF `seg_lt B C D E` `seg_eq D E B C`] .
		have "\<not> (seg_lt B C B C)" using trichotomy2[OF `seg_lt B C B C`] .
		show "False" using `\<not> (seg_lt B C B C)` `seg_lt B C B C` by blast
	qed
	hence "\<not> (bet A D B)" by blast
	have "\<not> (\<not> (bet A B D))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (bet A B D)))"
hence "\<not> (bet A B D)" by blast
		have "bet A D E" using `bet A D E` .
		have "bet A B E" using n3_6b[OF `bet A B C` `bet A C E`] .
		have "B = D" using connectivityE[OF `bet A B E` `bet A D E` `\<not> (bet A B D)` `\<not> (bet A D B)`] .
		have "seg_eq A B A B" using congruencereflexiveE.
		have "seg_eq A B A D" using `seg_eq A B A B` `B = D` by blast
		have "seg_eq A C A E" using sumofparts[OF `seg_eq A B A D` `seg_eq B C D E` `bet A B C` `bet A D E`] .
		have "bet A B E" using `bet A B E` by blast
		have "A \<noteq> B" using betweennotequal[OF `bet A B C`] by blast
		have "ray_on A B E" using ray4 `bet A B E` `A \<noteq> B` by blast
		have "ray_on A B C" using ray4 `bet A B C` `A \<noteq> B` by blast
		have "C = E" using layoffunique[OF `ray_on A B C` `ray_on A B E` `seg_eq A C A E`] .
		have "C \<noteq> E" using betweennotequal[OF `bet A C E`] by blast
		show "False" using `C \<noteq> E` `C = E` by blast
	qed
	hence "bet A B D" by blast
	thus ?thesis by blast
qed

end