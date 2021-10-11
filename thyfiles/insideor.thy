theory insideor
	imports n3_6a Geometry lessthancongruence
begin

theorem(in euclidean_geometry) insideor:
	assumes 
		"circle J C P Q"
		"cir_in A J"
	shows "A = C \<or> seg_lt C A P Q"
proof -
	obtain D E where "circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E" using inside_f[OF `circle J C P Q` `cir_in A J`]  by  blast
	have "seg_eq C E P Q" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	have "seg_eq C D P Q" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	have "bet D A E" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
	consider "A = C"|"A \<noteq> C" by blast
	hence "A = C \<or> seg_lt C A P Q"
	proof (cases)
		assume "A = C"
		have "A = C \<or> seg_lt C A P Q" using `A = C` by blast
		thus ?thesis by blast
	next
		assume "A \<noteq> C"
		have "\<not> (\<not> (seg_lt C A P Q))"
		proof (rule ccontr)
			assume "\<not> (\<not> (\<not> (seg_lt C A P Q)))"
hence "\<not> (seg_lt C A P Q)" by blast
			have "\<not> (bet D A C)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet D A C))"
hence "bet D A C" by blast
				have "bet C A D" using betweennesssymmetryE[OF `bet D A C`] .
				have "seg_eq C A C A" using congruencereflexiveE.
				have "seg_lt C A C D" using lessthan_b[OF `bet C A D` `seg_eq C A C A`] .
				have "seg_lt C A P Q" using lessthancongruence[OF `seg_lt C A C D` `seg_eq C D P Q`] .
				show "False" using `seg_lt C A P Q` `\<not> (seg_lt C A P Q)` by blast
			qed
			hence "\<not> (bet D A C)" by blast
			have "\<not> (bet D C A)"
			proof (rule ccontr)
				assume "\<not> (\<not> (bet D C A))"
hence "bet D C A" by blast
				have "bet C A E" using n3_6a[OF `bet D C A` `bet D A E`] .
				have "seg_eq C A C A" using congruencereflexiveE.
				have "seg_lt C A C E" using lessthan_b[OF `bet C A E` `seg_eq C A C A`] .
				have "seg_lt C A P Q" using lessthancongruence[OF `seg_lt C A C E` `seg_eq C E P Q`] .
				show "False" using `seg_lt C A P Q` `\<not> (seg_lt C A P Q)` by blast
			qed
			hence "\<not> (bet D C A)" by blast
			have "bet D A E" using `bet D A E` .
			have "bet D C E" using `circle J C P Q \<and> bet D C E \<and> seg_eq C E P Q \<and> seg_eq C D P Q \<and> bet D A E` by blast
			have "A = C" using connectivityE[OF `bet D A E` `bet D C E` `\<not> (bet D A C)` `\<not> (bet D C A)`] .
			show "False" using `A = C` `A \<noteq> C` by blast
		qed
		hence "seg_lt C A P Q" by blast
		have "A = C \<or> seg_lt C A P Q" using `seg_lt C A P Q` by blast
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end