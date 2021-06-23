theory ray3
	imports n3_6a n3_7a Geometry outerconnectivity
begin

theorem ray3:
	assumes "axioms"
		"ray_on B C D"
		"ray_on B C V"
	shows "ray_on B D V"
proof -
	obtain E where "bet E B D \<and> bet E B C" using ray_f[OF `axioms` `ray_on B C D`]  by  blast
	obtain H where "bet H B V \<and> bet H B C" using ray_f[OF `axioms` `ray_on B C V`]  by  blast
	have "bet E B C" using `bet E B D \<and> bet E B C` by blast
	have "bet E B D" using `bet E B D \<and> bet E B C` by blast
	have "bet H B V" using `bet H B V \<and> bet H B C` by blast
	have "bet H B C" using `bet H B V \<and> bet H B C` by blast
	have "\<not> (\<not> (bet E B V))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (bet E B V)))"
hence "\<not> (bet E B V)" by blast
		have "\<not> (bet B E H)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet B E H))"
hence "bet B E H" by blast
			have "bet H E B" using betweennesssymmetryE[OF `axioms` `bet B E H`] .
			have "bet E B V" using n3_6a[OF `axioms` `bet H E B` `bet H B V`] .
			show "False" using `bet E B V` `\<not> (bet E B V)` by blast
		qed
		hence "\<not> (bet B E H)" by blast
		have "\<not> (bet B H E)"
		proof (rule ccontr)
			assume "\<not> (\<not> (bet B H E))"
hence "bet B H E" by blast
			have "bet E H B" using betweennesssymmetryE[OF `axioms` `bet B H E`] .
			have "bet E B V" using n3_7a[OF `axioms` `bet E H B` `bet H B V`] .
			show "False" using `bet E B V` `\<not> (bet E B V)` by blast
		qed
		hence "\<not> (bet B H E)" by blast
		have "bet C B E" using betweennesssymmetryE[OF `axioms` `bet E B C`] .
		have "bet C B H" using betweennesssymmetryE[OF `axioms` `bet H B C`] .
		have "H = E" using outerconnectivity[OF `axioms` `bet C B H` `bet C B E` `\<not> (bet B H E)` `\<not> (bet B E H)`] .
		have "bet E B V" using `bet H B V` `H = E` by blast
		show "False" using `bet E B V` `\<not> (bet E B V)` by blast
	qed
	hence "bet E B V" by blast
	have "ray_on B D V" using ray_b[OF `axioms` `bet E B V` `bet E B D`] .
	thus ?thesis by blast
qed

end