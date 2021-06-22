theory ray3
	imports Axioms Definitions Theorems
begin

theorem ray3:
	assumes: `axioms`
		"ray_on B C D"
		"ray_on B C V"
	shows: "ray_on B D V"
proof -
	obtain E where "bet E B D \<and> bet E B C" sorry
	obtain H where "bet H B V \<and> bet H B C" sorry
	have "bet E B C" using `bet E B D \<and> bet E B C` by blast
	have "bet E B D" using `bet E B D \<and> bet E B C` by blast
	have "bet H B V" using `bet H B V \<and> bet H B C` by blast
	have "bet H B C" using `bet H B V \<and> bet H B C` by blast
	have "bet E B V"
	proof (rule ccontr)
		assume "\<not> (bet E B V)"
		have "\<not> (bet B E H)"
		proof (rule ccontr)
			assume "bet B E H"
			have "bet H E B" using betweennesssymmetryE[OF `axioms` `bet B E H`] .
			have "bet E B V" using n3_6a[OF `axioms` `bet H E B` `bet H B V`] .
			show "False" using `bet E B V` `\<not> (bet E B V)` by blast
		qed
		hence "\<not> (bet B E H)" by blast
		have "\<not> (bet B H E)"
		proof (rule ccontr)
			assume "bet B H E"
			have "bet E H B" using betweennesssymmetryE[OF `axioms` `bet B H E`] .
			have "bet E B V" using n3_7a[OF `axioms` `bet E H B` `bet H B V`] .
			show "False" using `bet E B V` `\<not> (bet E B V)` by blast
		qed
		hence "\<not> (bet B H E)" by blast
		have "bet C B E" using betweennesssymmetryE[OF `axioms` `bet E B C`] .
		have "bet C B H" using betweennesssymmetryE[OF `axioms` `bet H B C`] .
		have "H = E" using outerconnectivity[OF `axioms` `bet C B H` `bet C B E` `\<not> (bet B H E)` `\<not> (bet B E H)`] .
		have "bet E B V" sorry
		show "False" using `bet E B V` `\<not> (bet E B V)` by blast
	qed
	hence "bet E B V" by blast
	have "ray_on B D V" sorry
	thus ?thesis by blast
qed

end