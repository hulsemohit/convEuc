theory layoffunique
	imports n3_6b Geometry congruenceflip congruencesymmetric differenceofparts equalitysymmetric extensionunique interior5 nullsegment3 partnotequalwhole ray1
begin

theorem(in euclidean_geometry) layoffunique:
	assumes 
		"ray_on A B C"
		"ray_on A B D"
		"seg_eq A C A D"
	shows "C = D"
proof -
	have "seg_eq A D A C" using congruencesymmetric[OF `seg_eq A C A D`] .
	have "bet A C B \<or> B = C \<or> bet A B C" using ray1[OF `ray_on A B C`] .
	have "bet A D B \<or> B = D \<or> bet A B D" using ray1[OF `ray_on A B D`] .
	have "seg_eq A B A B" using congruencereflexiveE.
	have "seg_eq C B C B" using congruencereflexiveE.
	have "seg_eq A C A C" using congruencereflexiveE.
	consider "bet A C B"|"B = C"|"bet A B C" using `bet A C B \<or> B = C \<or> bet A B C`  by blast
	hence "C = D"
	proof (cases)
		assume "bet A C B"
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence "C = D"
		proof (cases)
			assume "bet A D B"
			have "seg_eq C B D B" using differenceofparts[OF `seg_eq A C A D` `seg_eq A B A B` `bet A C B` `bet A D B`] .
			have "seg_eq B C B D" using congruenceflip[OF `seg_eq C B D B`] by blast
			have "seg_eq C C C D" using interior5[OF `bet A C B` `bet A C B` `seg_eq A C A C` `seg_eq C B C B` `seg_eq A C A D` `seg_eq B C B D`] .
			have "seg_eq C D C C" using congruencesymmetric[OF `seg_eq C C C D`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "C \<noteq> C" using nullsegment3[OF `C \<noteq> D` `seg_eq C D C C`] .
				have "C = C" using equalityreflexiveE.
				show "False" using `C = C` `C \<noteq> C` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		next
			assume "B = D"
			have "bet A C D" using `bet A C B` `B = D` by blast
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		next
			assume "bet A B D"
			have "bet A C D" using n3_6b[OF `bet A C B` `bet A B D`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	next
		assume "B = C"
		have "seg_eq A B A D" using `seg_eq A C A D` `B = C` by blast
		have "seg_eq A D A B" using congruencesymmetric[OF `seg_eq A B A D`] .
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence "C = D"
		proof (cases)
			assume "bet A D B"
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A D A B)" using partnotequalwhole[OF `bet A D B`] .
				show "False" using `\<not> (seg_eq A D A B)` `seg_eq A D A B` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		next
			assume "B = D"
			have "C = B" using equalitysymmetric[OF `B = C`] .
			have "D = B" using equalitysymmetric[OF `B = D`] .
			have "C = D" using equalitytransitiveE[OF `C = B` `D = B`] .
			thus ?thesis by blast
		next
			assume "bet A B D"
			have "bet A C D" using `bet A B D` `B = C` by blast
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A C A D)" using partnotequalwhole[OF `bet A C D`] .
				show "False" using `\<not> (seg_eq A C A D)` `seg_eq A C A D` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	next
		assume "bet A B C"
		consider "bet A D B"|"B = D"|"bet A B D" using `bet A D B \<or> B = D \<or> bet A B D`  by blast
		hence "C = D"
		proof (cases)
			assume "bet A D B"
			have "bet A D C" using n3_6b[OF `bet A D B` `bet A B C`] .
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A D A C)" using partnotequalwhole[OF `bet A D C`] .
				show "False" using `\<not> (seg_eq A D A C)` `seg_eq A D A C` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		next
			assume "B = D"
			have "bet A D C" using `bet A B C` `B = D` by blast
			have "\<not> (C \<noteq> D)"
			proof (rule ccontr)
				assume "\<not> (\<not> (C \<noteq> D))"
hence "C \<noteq> D" by blast
				have "\<not> (seg_eq A D A C)" using partnotequalwhole[OF `bet A D C`] .
				show "False" using `\<not> (seg_eq A D A C)` `seg_eq A D A C` by blast
			qed
			hence "C = D" by blast
			thus ?thesis by blast
		next
			assume "bet A B D"
			have "seg_eq B C B D" using differenceofparts[OF `seg_eq A B A B` `seg_eq A C A D` `bet A B C` `bet A B D`] .
			have "C = D" using extensionunique[OF `bet A B C` `bet A B D` `seg_eq B C B D`] .
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end