theory tworays
	imports Geometry ray1 raystrict
begin

theorem(in euclidean_geometry) tworays:
	assumes 
		"ray_on A B C"
		"ray_on B A C"
	shows "bet A C B"
proof -
	have "B \<noteq> C" using raystrict[OF `ray_on B A C`] .
	have "A \<noteq> C" using raystrict[OF `ray_on A B C`] .
	have "bet A C B \<or> B = C \<or> bet A B C" using ray1[OF `ray_on A B C`] .
	have "bet A C B \<or> bet A B C" using `bet A C B \<or> B = C \<or> bet A B C` `B \<noteq> C` by blast
	have "bet B C A \<or> A = C \<or> bet B A C" using ray1[OF `ray_on B A C`] .
	have "bet B C A \<or> bet B A C" using `bet B C A \<or> A = C \<or> bet B A C` `A \<noteq> C` by blast
	consider "bet A C B"|"bet A B C" using `bet A C B \<or> bet A B C`  by blast
	hence "bet A C B"
	proof (cases)
		assume "bet A C B"
		thus ?thesis by blast
	next
		assume "bet A B C"
		consider "bet B C A"|"bet B A C" using `bet B C A \<or> bet B A C`  by blast
		hence "bet A C B"
		proof (cases)
			assume "bet B C A"
			have "bet A C B" using betweennesssymmetryE[OF `bet B C A`] .
			thus ?thesis by blast
		next
			assume "bet B A C"
			have "\<not> (\<not> (bet A C B))"
			proof (rule ccontr)
				assume "\<not> (\<not> (\<not> (bet A C B)))"
hence "\<not> (bet A C B)" by blast
				have "bet A B A" using innertransitivityE[OF `bet A B C` `bet B A C`] .
				have "\<not> (bet A B A)" using betweennessidentityE.
				show "False" using `\<not> (bet A B A)` `bet A B A` by blast
			qed
			hence "bet A C B" by blast
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end